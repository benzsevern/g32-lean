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

def g32p_row21_groupLabel : Fin 972 → Fin 5 :=
  fun i => (if i.val < 486 then
(if i.val < 243 then
(if i.val < 121 then
(if i.val < 60 then
(if i.val < 30 then
(if i.val < 15 then
(if i.val < 7 then
(if i.val < 3 then
(if i.val < 1 then
0
else
(if i.val < 2 then
0
else
1))
else
(if i.val < 5 then
(if i.val < 4 then
2
else
3)
else
(if i.val < 6 then
4
else
0)))
else
(if i.val < 11 then
(if i.val < 9 then
(if i.val < 8 then
1
else
2)
else
(if i.val < 10 then
3
else
4))
else
(if i.val < 13 then
(if i.val < 12 then
1
else
2)
else
(if i.val < 14 then
3
else
4))))
else
(if i.val < 22 then
(if i.val < 18 then
(if i.val < 16 then
1
else
(if i.val < 17 then
2
else
3))
else
(if i.val < 20 then
(if i.val < 19 then
4
else
2)
else
(if i.val < 21 then
4
else
1)))
else
(if i.val < 26 then
(if i.val < 24 then
(if i.val < 23 then
2
else
3)
else
(if i.val < 25 then
4
else
1))
else
(if i.val < 28 then
(if i.val < 27 then
2
else
3)
else
(if i.val < 29 then
4
else
1)))))
else
(if i.val < 45 then
(if i.val < 37 then
(if i.val < 33 then
(if i.val < 31 then
2
else
(if i.val < 32 then
3
else
4))
else
(if i.val < 35 then
(if i.val < 34 then
2
else
4)
else
(if i.val < 36 then
2
else
3)))
else
(if i.val < 41 then
(if i.val < 39 then
(if i.val < 38 then
4
else
1)
else
(if i.val < 40 then
2
else
3))
else
(if i.val < 43 then
(if i.val < 42 then
4
else
2)
else
(if i.val < 44 then
4
else
1))))
else
(if i.val < 52 then
(if i.val < 48 then
(if i.val < 46 then
2
else
(if i.val < 47 then
3
else
4))
else
(if i.val < 50 then
(if i.val < 49 then
1
else
3)
else
(if i.val < 51 then
4
else
2)))
else
(if i.val < 56 then
(if i.val < 54 then
(if i.val < 53 then
4
else
1)
else
(if i.val < 55 then
2
else
3))
else
(if i.val < 58 then
(if i.val < 57 then
4
else
1)
else
(if i.val < 59 then
2
else
3))))))
else
(if i.val < 90 then
(if i.val < 75 then
(if i.val < 67 then
(if i.val < 63 then
(if i.val < 61 then
4
else
(if i.val < 62 then
1
else
2))
else
(if i.val < 65 then
(if i.val < 64 then
3
else
4)
else
(if i.val < 66 then
2
else
4)))
else
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
2
else
3)
else
(if i.val < 70 then
4
else
1))
else
(if i.val < 73 then
(if i.val < 72 then
2
else
3)
else
(if i.val < 74 then
4
else
2))))
else
(if i.val < 82 then
(if i.val < 78 then
(if i.val < 76 then
4
else
(if i.val < 77 then
1
else
2))
else
(if i.val < 80 then
(if i.val < 79 then
3
else
4)
else
(if i.val < 81 then
1
else
3)))
else
(if i.val < 86 then
(if i.val < 84 then
(if i.val < 83 then
4
else
2)
else
(if i.val < 85 then
4
else
1))
else
(if i.val < 88 then
(if i.val < 87 then
2
else
3)
else
(if i.val < 89 then
4
else
1)))))
else
(if i.val < 105 then
(if i.val < 97 then
(if i.val < 93 then
(if i.val < 91 then
2
else
(if i.val < 92 then
3
else
4))
else
(if i.val < 95 then
(if i.val < 94 then
2
else
4)
else
(if i.val < 96 then
1
else
2)))
else
(if i.val < 101 then
(if i.val < 99 then
(if i.val < 98 then
3
else
4)
else
(if i.val < 100 then
1
else
3))
else
(if i.val < 103 then
(if i.val < 102 then
4
else
2)
else
(if i.val < 104 then
4
else
1))))
else
(if i.val < 113 then
(if i.val < 109 then
(if i.val < 107 then
(if i.val < 106 then
2
else
3)
else
(if i.val < 108 then
4
else
2))
else
(if i.val < 111 then
(if i.val < 110 then
3
else
4)
else
(if i.val < 112 then
1
else
2)))
else
(if i.val < 117 then
(if i.val < 115 then
(if i.val < 114 then
3
else
4)
else
(if i.val < 116 then
2
else
4))
else
(if i.val < 119 then
(if i.val < 118 then
1
else
2)
else
(if i.val < 120 then
3
else
4)))))))
else
(if i.val < 182 then
(if i.val < 151 then
(if i.val < 136 then
(if i.val < 128 then
(if i.val < 124 then
(if i.val < 122 then
2
else
(if i.val < 123 then
4
else
2))
else
(if i.val < 126 then
(if i.val < 125 then
3
else
4)
else
(if i.val < 127 then
1
else
2)))
else
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
3
else
4)
else
(if i.val < 131 then
1
else
3))
else
(if i.val < 134 then
(if i.val < 133 then
4
else
4)
else
(if i.val < 135 then
2
else
3))))
else
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
4
else
(if i.val < 138 then
1
else
2))
else
(if i.val < 141 then
(if i.val < 140 then
3
else
4)
else
(if i.val < 142 then
2
else
4)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
1
else
2)
else
(if i.val < 146 then
3
else
4))
else
(if i.val < 149 then
(if i.val < 148 then
1
else
3)
else
(if i.val < 150 then
4
else
2)))))
else
(if i.val < 166 then
(if i.val < 158 then
(if i.val < 154 then
(if i.val < 152 then
4
else
(if i.val < 153 then
1
else
2))
else
(if i.val < 156 then
(if i.val < 155 then
3
else
4)
else
(if i.val < 157 then
1
else
2)))
else
(if i.val < 162 then
(if i.val < 160 then
(if i.val < 159 then
3
else
4)
else
(if i.val < 161 then
2
else
4))
else
(if i.val < 164 then
(if i.val < 163 then
1
else
2)
else
(if i.val < 165 then
3
else
4))))
else
(if i.val < 174 then
(if i.val < 170 then
(if i.val < 168 then
(if i.val < 167 then
1
else
3)
else
(if i.val < 169 then
4
else
2))
else
(if i.val < 172 then
(if i.val < 171 then
4
else
1)
else
(if i.val < 173 then
2
else
3)))
else
(if i.val < 178 then
(if i.val < 176 then
(if i.val < 175 then
4
else
2)
else
(if i.val < 177 then
3
else
4))
else
(if i.val < 180 then
(if i.val < 179 then
1
else
2)
else
(if i.val < 181 then
3
else
4))))))
else
(if i.val < 212 then
(if i.val < 197 then
(if i.val < 189 then
(if i.val < 185 then
(if i.val < 183 then
2
else
(if i.val < 184 then
4
else
1))
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
2)))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
4
else
2)
else
(if i.val < 192 then
3
else
4))
else
(if i.val < 195 then
(if i.val < 194 then
1
else
2)
else
(if i.val < 196 then
3
else
4))))
else
(if i.val < 204 then
(if i.val < 200 then
(if i.val < 198 then
1
else
(if i.val < 199 then
3
else
4))
else
(if i.val < 202 then
(if i.val < 201 then
4
else
1)
else
(if i.val < 203 then
2
else
3)))
else
(if i.val < 208 then
(if i.val < 206 then
(if i.val < 205 then
4
else
1)
else
(if i.val < 207 then
3
else
4))
else
(if i.val < 210 then
(if i.val < 209 then
2
else
4)
else
(if i.val < 211 then
1
else
2)))))
else
(if i.val < 227 then
(if i.val < 219 then
(if i.val < 215 then
(if i.val < 213 then
3
else
(if i.val < 214 then
4
else
2))
else
(if i.val < 217 then
(if i.val < 216 then
3
else
4)
else
(if i.val < 218 then
1
else
2)))
else
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
3
else
4)
else
(if i.val < 222 then
2
else
4))
else
(if i.val < 225 then
(if i.val < 224 then
1
else
2)
else
(if i.val < 226 then
3
else
4))))
else
(if i.val < 235 then
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
2
else
4)
else
(if i.val < 230 then
2
else
3))
else
(if i.val < 233 then
(if i.val < 232 then
4
else
1)
else
(if i.val < 234 then
2
else
4)))
else
(if i.val < 239 then
(if i.val < 237 then
(if i.val < 236 then
1
else
3)
else
(if i.val < 238 then
4
else
4))
else
(if i.val < 241 then
(if i.val < 240 then
1
else
2)
else
(if i.val < 242 then
3
else
4))))))))
else
(if i.val < 364 then
(if i.val < 303 then
(if i.val < 273 then
(if i.val < 258 then
(if i.val < 250 then
(if i.val < 246 then
(if i.val < 244 then
2
else
(if i.val < 245 then
4
else
1))
else
(if i.val < 248 then
(if i.val < 247 then
2
else
3)
else
(if i.val < 249 then
4
else
3)))
else
(if i.val < 254 then
(if i.val < 252 then
(if i.val < 251 then
4
else
2)
else
(if i.val < 253 then
4
else
2))
else
(if i.val < 256 then
(if i.val < 255 then
3
else
4)
else
(if i.val < 257 then
2
else
3))))
else
(if i.val < 265 then
(if i.val < 261 then
(if i.val < 259 then
4
else
(if i.val < 260 then
2
else
3))
else
(if i.val < 263 then
(if i.val < 262 then
4
else
2)
else
(if i.val < 264 then
4
else
2)))
else
(if i.val < 269 then
(if i.val < 267 then
(if i.val < 266 then
3
else
4)
else
(if i.val < 268 then
1
else
3))
else
(if i.val < 271 then
(if i.val < 270 then
4
else
4)
else
(if i.val < 272 then
2
else
3)))))
else
(if i.val < 288 then
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
4
else
(if i.val < 275 then
1
else
3))
else
(if i.val < 278 then
(if i.val < 277 then
4
else
2)
else
(if i.val < 279 then
4
else
1)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
3
else
4)
else
(if i.val < 283 then
4
else
1))
else
(if i.val < 286 then
(if i.val < 285 then
2
else
3)
else
(if i.val < 287 then
4
else
2))))
else
(if i.val < 295 then
(if i.val < 291 then
(if i.val < 289 then
4
else
(if i.val < 290 then
1
else
2))
else
(if i.val < 293 then
(if i.val < 292 then
4
else
1)
else
(if i.val < 294 then
3
else
4)))
else
(if i.val < 299 then
(if i.val < 297 then
(if i.val < 296 then
2
else
4)
else
(if i.val < 298 then
2
else
3))
else
(if i.val < 301 then
(if i.val < 300 then
4
else
2)
else
(if i.val < 302 then
3
else
4))))))
else
(if i.val < 333 then
(if i.val < 318 then
(if i.val < 310 then
(if i.val < 306 then
(if i.val < 304 then
1
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
2)
else
(if i.val < 309 then
4
else
1)))
else
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
2
else
3)
else
(if i.val < 313 then
4
else
2))
else
(if i.val < 316 then
(if i.val < 315 then
4
else
2)
else
(if i.val < 317 then
3
else
4))))
else
(if i.val < 325 then
(if i.val < 321 then
(if i.val < 319 then
1
else
(if i.val < 320 then
2
else
3))
else
(if i.val < 323 then
(if i.val < 322 then
4
else
1)
else
(if i.val < 324 then
3
else
4)))
else
(if i.val < 329 then
(if i.val < 327 then
(if i.val < 326 then
4
else
1)
else
(if i.val < 328 then
2
else
3))
else
(if i.val < 331 then
(if i.val < 330 then
4
else
1)
else
(if i.val < 332 then
3
else
4)))))
else
(if i.val < 348 then
(if i.val < 340 then
(if i.val < 336 then
(if i.val < 334 then
2
else
(if i.val < 335 then
4
else
1))
else
(if i.val < 338 then
(if i.val < 337 then
2
else
3)
else
(if i.val < 339 then
4
else
2)))
else
(if i.val < 344 then
(if i.val < 342 then
(if i.val < 341 then
3
else
4)
else
(if i.val < 343 then
1
else
2))
else
(if i.val < 346 then
(if i.val < 345 then
3
else
4)
else
(if i.val < 347 then
2
else
4))))
else
(if i.val < 356 then
(if i.val < 352 then
(if i.val < 350 then
(if i.val < 349 then
1
else
2)
else
(if i.val < 351 then
3
else
4))
else
(if i.val < 354 then
(if i.val < 353 then
2
else
4)
else
(if i.val < 355 then
2
else
3)))
else
(if i.val < 360 then
(if i.val < 358 then
(if i.val < 357 then
4
else
1)
else
(if i.val < 359 then
2
else
4))
else
(if i.val < 362 then
(if i.val < 361 then
1
else
3)
else
(if i.val < 363 then
4
else
4)))))))
else
(if i.val < 425 then
(if i.val < 394 then
(if i.val < 379 then
(if i.val < 371 then
(if i.val < 367 then
(if i.val < 365 then
1
else
(if i.val < 366 then
2
else
4))
else
(if i.val < 369 then
(if i.val < 368 then
2
else
4)
else
(if i.val < 370 then
1
else
2)))
else
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
3
else
4)
else
(if i.val < 374 then
3
else
4))
else
(if i.val < 377 then
(if i.val < 376 then
2
else
4)
else
(if i.val < 378 then
2
else
3))))
else
(if i.val < 386 then
(if i.val < 382 then
(if i.val < 380 then
4
else
(if i.val < 381 then
2
else
3))
else
(if i.val < 384 then
(if i.val < 383 then
4
else
2)
else
(if i.val < 385 then
3
else
4)))
else
(if i.val < 390 then
(if i.val < 388 then
(if i.val < 387 then
2
else
4)
else
(if i.val < 389 then
2
else
3))
else
(if i.val < 392 then
(if i.val < 391 then
4
else
1)
else
(if i.val < 393 then
4
else
4)))))
else
(if i.val < 409 then
(if i.val < 401 then
(if i.val < 397 then
(if i.val < 395 then
3
else
(if i.val < 396 then
4
else
1))
else
(if i.val < 399 then
(if i.val < 398 then
3
else
4)
else
(if i.val < 400 then
2
else
4)))
else
(if i.val < 405 then
(if i.val < 403 then
(if i.val < 402 then
1
else
3)
else
(if i.val < 404 then
4
else
4))
else
(if i.val < 407 then
(if i.val < 406 then
3
else
4)
else
(if i.val < 408 then
1
else
2))))
else
(if i.val < 417 then
(if i.val < 413 then
(if i.val < 411 then
(if i.val < 410 then
3
else
4)
else
(if i.val < 412 then
2
else
4))
else
(if i.val < 415 then
(if i.val < 414 then
1
else
2)
else
(if i.val < 416 then
3
else
4)))
else
(if i.val < 421 then
(if i.val < 419 then
(if i.val < 418 then
2
else
4)
else
(if i.val < 420 then
2
else
3))
else
(if i.val < 423 then
(if i.val < 422 then
4
else
1)
else
(if i.val < 424 then
2
else
4))))))
else
(if i.val < 455 then
(if i.val < 440 then
(if i.val < 432 then
(if i.val < 428 then
(if i.val < 426 then
1
else
(if i.val < 427 then
3
else
4))
else
(if i.val < 430 then
(if i.val < 429 then
4
else
1)
else
(if i.val < 431 then
2
else
3)))
else
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
4
else
2)
else
(if i.val < 435 then
4
else
1))
else
(if i.val < 438 then
(if i.val < 437 then
2
else
4)
else
(if i.val < 439 then
3
else
4))))
else
(if i.val < 447 then
(if i.val < 443 then
(if i.val < 441 then
2
else
(if i.val < 442 then
4
else
4))
else
(if i.val < 445 then
(if i.val < 444 then
2
else
3)
else
(if i.val < 446 then
4
else
2)))
else
(if i.val < 451 then
(if i.val < 449 then
(if i.val < 448 then
3
else
4)
else
(if i.val < 450 then
4
else
2))
else
(if i.val < 453 then
(if i.val < 452 then
3
else
4)
else
(if i.val < 454 then
1
else
3)))))
else
(if i.val < 470 then
(if i.val < 462 then
(if i.val < 458 then
(if i.val < 456 then
4
else
(if i.val < 457 then
4
else
2))
else
(if i.val < 460 then
(if i.val < 459 then
4
else
3)
else
(if i.val < 461 then
4
else
1)))
else
(if i.val < 466 then
(if i.val < 464 then
(if i.val < 463 then
3
else
4)
else
(if i.val < 465 then
4
else
2))
else
(if i.val < 468 then
(if i.val < 467 then
3
else
4)
else
(if i.val < 469 then
3
else
4))))
else
(if i.val < 478 then
(if i.val < 474 then
(if i.val < 472 then
(if i.val < 471 then
2
else
4)
else
(if i.val < 473 then
2
else
3))
else
(if i.val < 476 then
(if i.val < 475 then
4
else
2)
else
(if i.val < 477 then
3
else
4)))
else
(if i.val < 482 then
(if i.val < 480 then
(if i.val < 479 then
2
else
3)
else
(if i.val < 481 then
4
else
4))
else
(if i.val < 484 then
(if i.val < 483 then
2
else
4)
else
(if i.val < 485 then
2
else
3)))))))))
else
(if i.val < 729 then
(if i.val < 607 then
(if i.val < 546 then
(if i.val < 516 then
(if i.val < 501 then
(if i.val < 493 then
(if i.val < 489 then
(if i.val < 487 then
4
else
(if i.val < 488 then
3
else
4))
else
(if i.val < 491 then
(if i.val < 490 then
4
else
2)
else
(if i.val < 492 then
3
else
4)))
else
(if i.val < 497 then
(if i.val < 495 then
(if i.val < 494 then
2
else
4)
else
(if i.val < 496 then
3
else
4))
else
(if i.val < 499 then
(if i.val < 498 then
4
else
2)
else
(if i.val < 500 then
4
else
3))))
else
(if i.val < 508 then
(if i.val < 504 then
(if i.val < 502 then
4
else
(if i.val < 503 then
4
else
1))
else
(if i.val < 506 then
(if i.val < 505 then
3
else
4)
else
(if i.val < 507 then
4
else
1)))
else
(if i.val < 512 then
(if i.val < 510 then
(if i.val < 509 then
4
else
2)
else
(if i.val < 511 then
4
else
1))
else
(if i.val < 514 then
(if i.val < 513 then
3
else
4)
else
(if i.val < 515 then
4
else
3)))))
else
(if i.val < 531 then
(if i.val < 523 then
(if i.val < 519 then
(if i.val < 517 then
4
else
(if i.val < 518 then
3
else
4))
else
(if i.val < 521 then
(if i.val < 520 then
4
else
1)
else
(if i.val < 522 then
2
else
4)))
else
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
1
else
3)
else
(if i.val < 526 then
4
else
2))
else
(if i.val < 529 then
(if i.val < 528 then
4
else
2)
else
(if i.val < 530 then
3
else
4))))
else
(if i.val < 538 then
(if i.val < 534 then
(if i.val < 532 then
2
else
(if i.val < 533 then
4
else
2))
else
(if i.val < 536 then
(if i.val < 535 then
4
else
1)
else
(if i.val < 537 then
2
else
4)))
else
(if i.val < 542 then
(if i.val < 540 then
(if i.val < 539 then
2
else
4)
else
(if i.val < 541 then
2
else
3))
else
(if i.val < 544 then
(if i.val < 543 then
4
else
3)
else
(if i.val < 545 then
4
else
4))))))
else
(if i.val < 576 then
(if i.val < 561 then
(if i.val < 553 then
(if i.val < 549 then
(if i.val < 547 then
1
else
(if i.val < 548 then
2
else
4))
else
(if i.val < 551 then
(if i.val < 550 then
2
else
4)
else
(if i.val < 552 then
1
else
2)))
else
(if i.val < 557 then
(if i.val < 555 then
(if i.val < 554 then
4
else
3)
else
(if i.val < 556 then
4
else
2))
else
(if i.val < 559 then
(if i.val < 558 then
4
else
3)
else
(if i.val < 560 then
4
else
2))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
3
else
(if i.val < 563 then
4
else
2))
else
(if i.val < 566 then
(if i.val < 565 then
3
else
4)
else
(if i.val < 567 then
4
else
2)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
3
else
4)
else
(if i.val < 571 then
1
else
4))
else
(if i.val < 574 then
(if i.val < 573 then
4
else
3)
else
(if i.val < 575 then
4
else
3)))))
else
(if i.val < 591 then
(if i.val < 583 then
(if i.val < 579 then
(if i.val < 577 then
4
else
(if i.val < 578 then
2
else
4))
else
(if i.val < 581 then
(if i.val < 580 then
1
else
3)
else
(if i.val < 582 then
4
else
4)))
else
(if i.val < 587 then
(if i.val < 585 then
(if i.val < 584 then
4
else
1)
else
(if i.val < 586 then
2
else
3))
else
(if i.val < 589 then
(if i.val < 588 then
4
else
2)
else
(if i.val < 590 then
4
else
1))))
else
(if i.val < 599 then
(if i.val < 595 then
(if i.val < 593 then
(if i.val < 592 then
2
else
3)
else
(if i.val < 594 then
4
else
4))
else
(if i.val < 597 then
(if i.val < 596 then
3
else
4)
else
(if i.val < 598 then
2
else
4)))
else
(if i.val < 603 then
(if i.val < 601 then
(if i.val < 600 then
1
else
4)
else
(if i.val < 602 then
4
else
1))
else
(if i.val < 605 then
(if i.val < 604 then
2
else
4)
else
(if i.val < 606 then
2
else
4)))))))
else
(if i.val < 668 then
(if i.val < 637 then
(if i.val < 622 then
(if i.val < 614 then
(if i.val < 610 then
(if i.val < 608 then
1
else
(if i.val < 609 then
2
else
4))
else
(if i.val < 612 then
(if i.val < 611 then
3
else
4)
else
(if i.val < 613 then
2
else
4)))
else
(if i.val < 618 then
(if i.val < 616 then
(if i.val < 615 then
4
else
2)
else
(if i.val < 617 then
3
else
4))
else
(if i.val < 620 then
(if i.val < 619 then
2
else
3)
else
(if i.val < 621 then
4
else
4))))
else
(if i.val < 629 then
(if i.val < 625 then
(if i.val < 623 then
2
else
(if i.val < 624 then
3
else
4))
else
(if i.val < 627 then
(if i.val < 626 then
1
else
4)
else
(if i.val < 628 then
4
else
4)))
else
(if i.val < 633 then
(if i.val < 631 then
(if i.val < 630 then
3
else
4)
else
(if i.val < 632 then
1
else
3))
else
(if i.val < 635 then
(if i.val < 634 then
4
else
4)
else
(if i.val < 636 then
2
else
4)))))
else
(if i.val < 652 then
(if i.val < 644 then
(if i.val < 640 then
(if i.val < 638 then
3
else
(if i.val < 639 then
4
else
3))
else
(if i.val < 642 then
(if i.val < 641 then
4
else
2)
else
(if i.val < 643 then
3
else
4)))
else
(if i.val < 648 then
(if i.val < 646 then
(if i.val < 645 then
2
else
3)
else
(if i.val < 647 then
4
else
4))
else
(if i.val < 650 then
(if i.val < 649 then
2
else
4)
else
(if i.val < 651 then
2
else
3))))
else
(if i.val < 660 then
(if i.val < 656 then
(if i.val < 654 then
(if i.val < 653 then
4
else
4)
else
(if i.val < 655 then
4
else
2))
else
(if i.val < 658 then
(if i.val < 657 then
4
else
4)
else
(if i.val < 659 then
3
else
4)))
else
(if i.val < 664 then
(if i.val < 662 then
(if i.val < 661 then
4
else
2)
else
(if i.val < 663 then
4
else
4))
else
(if i.val < 666 then
(if i.val < 665 then
4
else
4)
else
(if i.val < 667 then
2
else
4))))))
else
(if i.val < 698 then
(if i.val < 683 then
(if i.val < 675 then
(if i.val < 671 then
(if i.val < 669 then
1
else
(if i.val < 670 then
3
else
4))
else
(if i.val < 673 then
(if i.val < 672 then
4
else
3)
else
(if i.val < 674 then
4
else
4)))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
4
else
2)
else
(if i.val < 678 then
4
else
1))
else
(if i.val < 681 then
(if i.val < 680 then
2
else
4)
else
(if i.val < 682 then
3
else
4))))
else
(if i.val < 690 then
(if i.val < 686 then
(if i.val < 684 then
2
else
(if i.val < 685 then
4
else
4))
else
(if i.val < 688 then
(if i.val < 687 then
3
else
4)
else
(if i.val < 689 then
2
else
3)))
else
(if i.val < 694 then
(if i.val < 692 then
(if i.val < 691 then
4
else
4)
else
(if i.val < 693 then
2
else
3))
else
(if i.val < 696 then
(if i.val < 695 then
4
else
1)
else
(if i.val < 697 then
4
else
4)))))
else
(if i.val < 713 then
(if i.val < 705 then
(if i.val < 701 then
(if i.val < 699 then
4
else
(if i.val < 700 then
3
else
4))
else
(if i.val < 703 then
(if i.val < 702 then
1
else
3)
else
(if i.val < 704 then
4
else
4)))
else
(if i.val < 709 then
(if i.val < 707 then
(if i.val < 706 then
2
else
4)
else
(if i.val < 708 then
3
else
4))
else
(if i.val < 711 then
(if i.val < 710 then
2
else
4)
else
(if i.val < 712 then
2
else
4))))
else
(if i.val < 721 then
(if i.val < 717 then
(if i.val < 715 then
(if i.val < 714 then
2
else
4)
else
(if i.val < 716 then
4
else
4))
else
(if i.val < 719 then
(if i.val < 718 then
2
else
4)
else
(if i.val < 720 then
2
else
3)))
else
(if i.val < 725 then
(if i.val < 723 then
(if i.val < 722 then
4
else
2)
else
(if i.val < 724 then
4
else
4))
else
(if i.val < 727 then
(if i.val < 726 then
4
else
3)
else
(if i.val < 728 then
4
else
4))))))))
else
(if i.val < 850 then
(if i.val < 789 then
(if i.val < 759 then
(if i.val < 744 then
(if i.val < 736 then
(if i.val < 732 then
(if i.val < 730 then
1
else
(if i.val < 731 then
3
else
4))
else
(if i.val < 734 then
(if i.val < 733 then
4
else
4)
else
(if i.val < 735 then
4
else
3)))
else
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
4
else
4)
else
(if i.val < 739 then
2
else
3))
else
(if i.val < 742 then
(if i.val < 741 then
4
else
4)
else
(if i.val < 743 then
2
else
4))))
else
(if i.val < 751 then
(if i.val < 747 then
(if i.val < 745 then
2
else
(if i.val < 746 then
3
else
4))
else
(if i.val < 749 then
(if i.val < 748 then
1
else
4)
else
(if i.val < 750 then
4
else
2)))
else
(if i.val < 755 then
(if i.val < 753 then
(if i.val < 752 then
3
else
4)
else
(if i.val < 754 then
2
else
4))
else
(if i.val < 757 then
(if i.val < 756 then
4
else
4)
else
(if i.val < 758 then
4
else
3)))))
else
(if i.val < 774 then
(if i.val < 766 then
(if i.val < 762 then
(if i.val < 760 then
4
else
(if i.val < 761 then
4
else
4))
else
(if i.val < 764 then
(if i.val < 763 then
3
else
4)
else
(if i.val < 765 then
4
else
2)))
else
(if i.val < 770 then
(if i.val < 768 then
(if i.val < 767 then
3
else
4)
else
(if i.val < 769 then
4
else
3))
else
(if i.val < 772 then
(if i.val < 771 then
4
else
4)
else
(if i.val < 773 then
4
else
4))))
else
(if i.val < 781 then
(if i.val < 777 then
(if i.val < 775 then
4
else
(if i.val < 776 then
3
else
4))
else
(if i.val < 779 then
(if i.val < 778 then
3
else
4)
else
(if i.val < 780 then
4
else
4)))
else
(if i.val < 785 then
(if i.val < 783 then
(if i.val < 782 then
4
else
4)
else
(if i.val < 784 then
2
else
4))
else
(if i.val < 787 then
(if i.val < 786 then
1
else
2)
else
(if i.val < 788 then
4
else
4))))))
else
(if i.val < 819 then
(if i.val < 804 then
(if i.val < 796 then
(if i.val < 792 then
(if i.val < 790 then
3
else
(if i.val < 791 then
4
else
4))
else
(if i.val < 794 then
(if i.val < 793 then
4
else
2)
else
(if i.val < 795 then
4
else
4)))
else
(if i.val < 800 then
(if i.val < 798 then
(if i.val < 797 then
2
else
4)
else
(if i.val < 799 then
4
else
2))
else
(if i.val < 802 then
(if i.val < 801 then
3
else
4)
else
(if i.val < 803 then
4
else
4))))
else
(if i.val < 811 then
(if i.val < 807 then
(if i.val < 805 then
4
else
(if i.val < 806 then
2
else
4))
else
(if i.val < 809 then
(if i.val < 808 then
3
else
4)
else
(if i.val < 810 then
3
else
4)))
else
(if i.val < 815 then
(if i.val < 813 then
(if i.val < 812 then
2
else
4)
else
(if i.val < 814 then
4
else
4))
else
(if i.val < 817 then
(if i.val < 816 then
2
else
3)
else
(if i.val < 818 then
4
else
4)))))
else
(if i.val < 834 then
(if i.val < 826 then
(if i.val < 822 then
(if i.val < 820 then
2
else
(if i.val < 821 then
4
else
4))
else
(if i.val < 824 then
(if i.val < 823 then
4
else
4)
else
(if i.val < 825 then
4
else
4)))
else
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
4
else
2)
else
(if i.val < 829 then
4
else
4))
else
(if i.val < 832 then
(if i.val < 831 then
3
else
4)
else
(if i.val < 833 then
4
else
4))))
else
(if i.val < 842 then
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
1
else
2)
else
(if i.val < 837 then
4
else
3))
else
(if i.val < 840 then
(if i.val < 839 then
4
else
4)
else
(if i.val < 841 then
4
else
4)))
else
(if i.val < 846 then
(if i.val < 844 then
(if i.val < 843 then
2
else
3)
else
(if i.val < 845 then
4
else
4))
else
(if i.val < 848 then
(if i.val < 847 then
4
else
4)
else
(if i.val < 849 then
4
else
2)))))))
else
(if i.val < 911 then
(if i.val < 880 then
(if i.val < 865 then
(if i.val < 857 then
(if i.val < 853 then
(if i.val < 851 then
4
else
(if i.val < 852 then
3
else
4))
else
(if i.val < 855 then
(if i.val < 854 then
4
else
2)
else
(if i.val < 856 then
4
else
4)))
else
(if i.val < 861 then
(if i.val < 859 then
(if i.val < 858 then
4
else
2)
else
(if i.val < 860 then
4
else
2))
else
(if i.val < 863 then
(if i.val < 862 then
4
else
4)
else
(if i.val < 864 then
4
else
4))))
else
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
4
else
(if i.val < 867 then
4
else
4))
else
(if i.val < 870 then
(if i.val < 869 then
4
else
4)
else
(if i.val < 871 then
4
else
2)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
3
else
4)
else
(if i.val < 875 then
4
else
4))
else
(if i.val < 878 then
(if i.val < 877 then
2
else
4)
else
(if i.val < 879 then
4
else
4)))))
else
(if i.val < 895 then
(if i.val < 887 then
(if i.val < 883 then
(if i.val < 881 then
4
else
(if i.val < 882 then
4
else
4))
else
(if i.val < 885 then
(if i.val < 884 then
4
else
4)
else
(if i.val < 886 then
4
else
4)))
else
(if i.val < 891 then
(if i.val < 889 then
(if i.val < 888 then
4
else
4)
else
(if i.val < 890 then
4
else
4))
else
(if i.val < 893 then
(if i.val < 892 then
4
else
4)
else
(if i.val < 894 then
4
else
4))))
else
(if i.val < 903 then
(if i.val < 899 then
(if i.val < 897 then
(if i.val < 896 then
2
else
4)
else
(if i.val < 898 then
4
else
4))
else
(if i.val < 901 then
(if i.val < 900 then
4
else
4)
else
(if i.val < 902 then
4
else
4)))
else
(if i.val < 907 then
(if i.val < 905 then
(if i.val < 904 then
4
else
4)
else
(if i.val < 906 then
4
else
4))
else
(if i.val < 909 then
(if i.val < 908 then
4
else
2)
else
(if i.val < 910 then
4
else
4))))))
else
(if i.val < 941 then
(if i.val < 926 then
(if i.val < 918 then
(if i.val < 914 then
(if i.val < 912 then
4
else
(if i.val < 913 then
4
else
4))
else
(if i.val < 916 then
(if i.val < 915 then
4
else
2)
else
(if i.val < 917 then
4
else
4)))
else
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
4
else
4)
else
(if i.val < 921 then
4
else
4))
else
(if i.val < 924 then
(if i.val < 923 then
4
else
4)
else
(if i.val < 925 then
4
else
4))))
else
(if i.val < 933 then
(if i.val < 929 then
(if i.val < 927 then
4
else
(if i.val < 928 then
4
else
4))
else
(if i.val < 931 then
(if i.val < 930 then
2
else
4)
else
(if i.val < 932 then
4
else
4)))
else
(if i.val < 937 then
(if i.val < 935 then
(if i.val < 934 then
4
else
4)
else
(if i.val < 936 then
4
else
4))
else
(if i.val < 939 then
(if i.val < 938 then
4
else
4)
else
(if i.val < 940 then
4
else
4)))))
else
(if i.val < 956 then
(if i.val < 948 then
(if i.val < 944 then
(if i.val < 942 then
4
else
(if i.val < 943 then
4
else
4))
else
(if i.val < 946 then
(if i.val < 945 then
4
else
4)
else
(if i.val < 947 then
4
else
4)))
else
(if i.val < 952 then
(if i.val < 950 then
(if i.val < 949 then
4
else
4)
else
(if i.val < 951 then
4
else
4))
else
(if i.val < 954 then
(if i.val < 953 then
4
else
4)
else
(if i.val < 955 then
4
else
4))))
else
(if i.val < 964 then
(if i.val < 960 then
(if i.val < 958 then
(if i.val < 957 then
4
else
4)
else
(if i.val < 959 then
4
else
4))
else
(if i.val < 962 then
(if i.val < 961 then
4
else
4)
else
(if i.val < 963 then
4
else
4)))
else
(if i.val < 968 then
(if i.val < 966 then
(if i.val < 965 then
4
else
4)
else
(if i.val < 967 then
4
else
4))
else
(if i.val < 970 then
(if i.val < 969 then
4
else
4)
else
(if i.val < 971 then
4
else
4))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row21_groupNext : Fin 972 → Fin 5 → Fin 972 :=
  fun i => (if i.val < 486 then
(if i.val < 243 then
(if i.val < 121 then
(if i.val < 60 then
(if i.val < 30 then
(if i.val < 15 then
(if i.val < 7 then
(if i.val < 3 then
(if i.val < 1 then
![1, 2, 3, 4, 5]
else
(if i.val < 2 then
![6, 7, 8, 9, 10]
else
![7, 11, 12, 13, 14]))
else
(if i.val < 5 then
(if i.val < 4 then
![8, 15, 16, 17, 18]
else
![9, 13, 19, 0, 20])
else
(if i.val < 6 then
![10, 14, 18, 20, 0]
else
![0, 21, 22, 23, 24])))
else
(if i.val < 11 then
(if i.val < 9 then
(if i.val < 8 then
![21, 25, 26, 27, 28]
else
![22, 29, 30, 31, 32])
else
(if i.val < 10 then
![23, 27, 33, 1, 34]
else
![24, 28, 32, 34, 1]))
else
(if i.val < 13 then
(if i.val < 12 then
![25, 0, 35, 36, 37]
else
![26, 38, 39, 40, 41])
else
(if i.val < 14 then
![27, 36, 42, 2, 43]
else
![28, 37, 41, 43, 2]))))
else
(if i.val < 22 then
(if i.val < 18 then
(if i.val < 16 then
![29, 44, 45, 46, 47]
else
(if i.val < 17 then
![30, 48, 0, 49, 50]
else
![31, 46, 51, 3, 52]))
else
(if i.val < 20 then
(if i.val < 19 then
![32, 47, 50, 52, 3]
else
![33, 53, 54, 55, 56])
else
(if i.val < 21 then
![34, 43, 56, 5, 4]
else
![2, 57, 58, 59, 60])))
else
(if i.val < 26 then
(if i.val < 24 then
(if i.val < 23 then
![3, 61, 62, 63, 64]
else
![4, 59, 65, 6, 66])
else
(if i.val < 25 then
![5, 60, 64, 66, 6]
else
![57, 1, 67, 68, 69]))
else
(if i.val < 28 then
(if i.val < 27 then
![58, 70, 71, 72, 73]
else
![59, 68, 74, 7, 75])
else
(if i.val < 29 then
![60, 69, 73, 75, 7]
else
![61, 76, 77, 78, 79])))))
else
(if i.val < 45 then
(if i.val < 37 then
(if i.val < 33 then
(if i.val < 31 then
![62, 80, 1, 81, 82]
else
(if i.val < 32 then
![63, 78, 83, 8, 84]
else
![64, 79, 82, 84, 8]))
else
(if i.val < 35 then
(if i.val < 34 then
![65, 85, 86, 87, 88]
else
![66, 75, 88, 10, 9])
else
(if i.val < 36 then
![67, 89, 90, 91, 92]
else
![68, 4, 93, 11, 94])))
else
(if i.val < 41 then
(if i.val < 39 then
(if i.val < 38 then
![69, 5, 92, 94, 11]
else
![70, 95, 96, 97, 98])
else
(if i.val < 40 then
![71, 99, 2, 100, 101]
else
![72, 97, 102, 12, 103]))
else
(if i.val < 43 then
(if i.val < 42 then
![73, 98, 101, 103, 12]
else
![74, 104, 105, 106, 107])
else
(if i.val < 44 then
![75, 94, 107, 14, 13]
else
![76, 3, 108, 109, 110]))))
else
(if i.val < 52 then
(if i.val < 48 then
(if i.val < 46 then
![77, 111, 112, 113, 114]
else
(if i.val < 47 then
![78, 109, 115, 15, 116]
else
![79, 110, 114, 116, 15]))
else
(if i.val < 50 then
(if i.val < 49 then
![80, 117, 118, 119, 120]
else
![81, 119, 121, 16, 122])
else
(if i.val < 51 then
![82, 120, 5, 122, 16]
else
![83, 102, 123, 124, 125])))
else
(if i.val < 56 then
(if i.val < 54 then
(if i.val < 53 then
![84, 116, 125, 18, 17]
else
![85, 126, 127, 128, 129])
else
(if i.val < 55 then
![86, 130, 4, 131, 132]
else
![87, 128, 124, 19, 133]))
else
(if i.val < 58 then
(if i.val < 57 then
![88, 129, 132, 133, 19]
else
![11, 6, 134, 135, 136])
else
(if i.val < 59 then
![12, 137, 138, 139, 140]
else
![13, 135, 141, 21, 142]))))))
else
(if i.val < 90 then
(if i.val < 75 then
(if i.val < 67 then
(if i.val < 63 then
(if i.val < 61 then
![14, 136, 140, 142, 21]
else
(if i.val < 62 then
![15, 143, 144, 145, 146]
else
![16, 147, 6, 148, 149]))
else
(if i.val < 65 then
(if i.val < 64 then
![17, 145, 150, 22, 151]
else
![18, 146, 149, 151, 22])
else
(if i.val < 66 then
![19, 152, 153, 154, 155]
else
![20, 142, 155, 24, 23])))
else
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
![134, 156, 157, 158, 159]
else
![135, 9, 160, 25, 161])
else
(if i.val < 70 then
![136, 10, 159, 161, 25]
else
![137, 162, 163, 164, 165]))
else
(if i.val < 73 then
(if i.val < 72 then
![138, 166, 7, 167, 168]
else
![139, 164, 169, 26, 170])
else
(if i.val < 74 then
![140, 165, 168, 170, 26]
else
![141, 171, 172, 173, 174]))))
else
(if i.val < 82 then
(if i.val < 78 then
(if i.val < 76 then
![142, 161, 174, 28, 27]
else
(if i.val < 77 then
![143, 8, 175, 176, 177]
else
![144, 178, 179, 180, 181]))
else
(if i.val < 80 then
(if i.val < 79 then
![145, 176, 182, 29, 183]
else
![146, 177, 181, 183, 29])
else
(if i.val < 81 then
![147, 184, 185, 186, 187]
else
![148, 186, 188, 30, 189])))
else
(if i.val < 86 then
(if i.val < 84 then
(if i.val < 83 then
![149, 187, 10, 189, 30]
else
![150, 169, 190, 191, 192])
else
(if i.val < 85 then
![151, 183, 192, 32, 31]
else
![152, 193, 194, 195, 196]))
else
(if i.val < 88 then
(if i.val < 87 then
![153, 197, 9, 198, 199]
else
![154, 195, 191, 33, 200])
else
(if i.val < 89 then
![155, 196, 199, 200, 33]
else
![156, 201, 202, 203, 204])))))
else
(if i.val < 105 then
(if i.val < 97 then
(if i.val < 93 then
(if i.val < 91 then
![157, 205, 11, 206, 207]
else
(if i.val < 92 then
![158, 203, 208, 35, 209]
else
![159, 204, 207, 209, 35]))
else
(if i.val < 95 then
(if i.val < 94 then
![160, 210, 211, 212, 213]
else
![161, 20, 213, 37, 36])
else
(if i.val < 96 then
![162, 12, 214, 215, 216]
else
![163, 217, 218, 219, 220])))
else
(if i.val < 101 then
(if i.val < 99 then
(if i.val < 98 then
![164, 215, 221, 38, 222]
else
![165, 216, 220, 222, 38])
else
(if i.val < 100 then
![166, 223, 224, 225, 226]
else
![167, 225, 227, 39, 228]))
else
(if i.val < 103 then
(if i.val < 102 then
![168, 226, 14, 228, 39]
else
![169, 208, 229, 230, 231])
else
(if i.val < 104 then
![170, 222, 231, 41, 40]
else
![171, 232, 233, 175, 234]))))
else
(if i.val < 113 then
(if i.val < 109 then
(if i.val < 107 then
(if i.val < 106 then
![172, 235, 13, 236, 237]
else
![173, 175, 230, 42, 238])
else
(if i.val < 108 then
![174, 234, 237, 238, 42]
else
![175, 239, 240, 241, 242]))
else
(if i.val < 111 then
(if i.val < 110 then
![176, 17, 243, 44, 244]
else
![177, 18, 242, 244, 44])
else
(if i.val < 112 then
![178, 245, 246, 247, 248]
else
![179, 218, 15, 249, 250])))
else
(if i.val < 117 then
(if i.val < 115 then
(if i.val < 114 then
![180, 247, 251, 45, 252]
else
![181, 248, 250, 252, 45])
else
(if i.val < 116 then
![182, 221, 253, 254, 255]
else
![183, 244, 255, 47, 46]))
else
(if i.val < 119 then
(if i.val < 118 then
![184, 16, 256, 257, 258]
else
![185, 224, 259, 260, 261])
else
(if i.val < 120 then
![186, 257, 262, 48, 263]
else
![187, 258, 261, 263, 48])))))))
else
(if i.val < 182 then
(if i.val < 151 then
(if i.val < 136 then
(if i.val < 128 then
(if i.val < 124 then
(if i.val < 122 then
![188, 251, 264, 265, 266]
else
(if i.val < 123 then
![189, 263, 266, 50, 49]
else
![190, 267, 17, 268, 269]))
else
(if i.val < 126 then
(if i.val < 125 then
![191, 230, 265, 51, 270]
else
![192, 231, 269, 270, 51])
else
(if i.val < 127 then
![193, 19, 271, 272, 273]
else
![194, 274, 260, 275, 276])))
else
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
![195, 272, 277, 53, 278]
else
![196, 273, 276, 278, 53])
else
(if i.val < 131 then
![197, 279, 249, 280, 281]
else
![198, 280, 268, 54, 282]))
else
(if i.val < 134 then
(if i.val < 133 then
![199, 281, 20, 282, 54]
else
![200, 278, 270, 56, 55])
else
(if i.val < 135 then
![35, 283, 284, 285, 286]
else
![36, 23, 287, 57, 288]))))
else
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
![37, 24, 286, 288, 57]
else
(if i.val < 138 then
![38, 289, 290, 271, 291]
else
![39, 292, 21, 293, 294]))
else
(if i.val < 141 then
(if i.val < 140 then
![40, 271, 295, 58, 296]
else
![41, 291, 294, 296, 58])
else
(if i.val < 142 then
![42, 241, 297, 298, 299]
else
![43, 288, 299, 60, 59])))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
![44, 22, 300, 301, 302]
else
![45, 303, 304, 305, 306])
else
(if i.val < 146 then
![46, 301, 307, 61, 308]
else
![47, 302, 306, 308, 61]))
else
(if i.val < 149 then
(if i.val < 148 then
![48, 309, 310, 311, 312]
else
![49, 311, 313, 62, 314])
else
(if i.val < 150 then
![50, 312, 24, 314, 62]
else
![51, 295, 315, 316, 317])))))
else
(if i.val < 166 then
(if i.val < 158 then
(if i.val < 154 then
(if i.val < 152 then
![52, 308, 317, 64, 63]
else
(if i.val < 153 then
![53, 318, 319, 320, 321]
else
![54, 322, 23, 323, 324]))
else
(if i.val < 156 then
(if i.val < 155 then
![55, 320, 316, 65, 325]
else
![56, 321, 324, 325, 65])
else
(if i.val < 157 then
![283, 326, 327, 328, 329]
else
![284, 330, 25, 331, 332])))
else
(if i.val < 162 then
(if i.val < 160 then
(if i.val < 159 then
![285, 328, 333, 67, 334]
else
![286, 329, 332, 334, 67])
else
(if i.val < 161 then
![287, 335, 336, 337, 338]
else
![288, 34, 338, 69, 68]))
else
(if i.val < 164 then
(if i.val < 163 then
![289, 26, 339, 340, 341]
else
![290, 342, 343, 344, 345])
else
(if i.val < 165 then
![271, 340, 346, 70, 347]
else
![291, 341, 345, 347, 70]))))
else
(if i.val < 174 then
(if i.val < 170 then
(if i.val < 168 then
(if i.val < 167 then
![292, 348, 349, 350, 351]
else
![293, 350, 352, 71, 353])
else
(if i.val < 169 then
![294, 351, 28, 353, 71]
else
![295, 333, 354, 355, 356]))
else
(if i.val < 172 then
(if i.val < 171 then
![296, 347, 356, 73, 72]
else
![241, 357, 358, 300, 359])
else
(if i.val < 173 then
![297, 360, 27, 361, 362]
else
![298, 300, 355, 74, 363])))
else
(if i.val < 178 then
(if i.val < 176 then
(if i.val < 175 then
![299, 359, 362, 363, 74]
else
![300, 364, 365, 104, 366])
else
(if i.val < 177 then
![301, 31, 367, 76, 368]
else
![302, 32, 366, 368, 76]))
else
(if i.val < 180 then
(if i.val < 179 then
![303, 369, 370, 371, 372]
else
![304, 343, 29, 373, 374])
else
(if i.val < 181 then
![305, 371, 375, 77, 376]
else
![306, 372, 374, 376, 77]))))))
else
(if i.val < 212 then
(if i.val < 197 then
(if i.val < 189 then
(if i.val < 185 then
(if i.val < 183 then
![307, 346, 377, 378, 379]
else
(if i.val < 184 then
![308, 368, 379, 79, 78]
else
![309, 30, 380, 381, 382]))
else
(if i.val < 187 then
(if i.val < 186 then
![310, 349, 383, 384, 385]
else
![311, 381, 386, 80, 387])
else
(if i.val < 188 then
![312, 382, 385, 387, 80]
else
![313, 375, 388, 389, 390])))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
![314, 387, 390, 82, 81]
else
![315, 391, 31, 217, 392])
else
(if i.val < 192 then
![316, 355, 389, 83, 393]
else
![317, 356, 392, 393, 83]))
else
(if i.val < 195 then
(if i.val < 194 then
![318, 33, 97, 394, 395]
else
![319, 396, 384, 397, 398])
else
(if i.val < 196 then
![320, 394, 399, 85, 400]
else
![321, 395, 398, 400, 85]))))
else
(if i.val < 204 then
(if i.val < 200 then
(if i.val < 198 then
![322, 401, 373, 402, 403]
else
(if i.val < 199 then
![323, 402, 217, 86, 404]
else
![324, 403, 34, 404, 86]))
else
(if i.val < 202 then
(if i.val < 201 then
![325, 400, 393, 88, 87]
else
![326, 35, 320, 405, 406])
else
(if i.val < 203 then
![327, 407, 408, 409, 410]
else
![328, 405, 411, 89, 412])))
else
(if i.val < 208 then
(if i.val < 206 then
(if i.val < 205 then
![329, 406, 410, 412, 89]
else
![330, 413, 414, 415, 416])
else
(if i.val < 207 then
![331, 415, 417, 90, 418]
else
![332, 416, 37, 418, 90]))
else
(if i.val < 210 then
(if i.val < 209 then
![333, 51, 419, 420, 421]
else
![334, 412, 421, 92, 91])
else
(if i.val < 211 then
![335, 422, 423, 339, 424]
else
![336, 425, 36, 426, 427])))))
else
(if i.val < 227 then
(if i.val < 219 then
(if i.val < 215 then
(if i.val < 213 then
![337, 339, 420, 93, 428]
else
(if i.val < 214 then
![338, 424, 427, 428, 93]
else
![339, 429, 430, 431, 432]))
else
(if i.val < 217 then
(if i.val < 216 then
![340, 40, 433, 95, 434]
else
![341, 41, 432, 434, 95])
else
(if i.val < 218 then
![342, 435, 436, 190, 437]
else
![343, 408, 38, 438, 439])))
else
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
![344, 190, 440, 96, 441]
else
![345, 437, 439, 441, 96])
else
(if i.val < 222 then
![346, 411, 193, 380, 442]
else
![347, 434, 442, 98, 97]))
else
(if i.val < 225 then
(if i.val < 224 then
![348, 39, 443, 444, 445]
else
![349, 414, 446, 447, 448])
else
(if i.val < 226 then
![350, 444, 176, 99, 449]
else
![351, 445, 448, 449, 99]))))
else
(if i.val < 235 then
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
![352, 440, 450, 451, 452]
else
![353, 449, 452, 101, 100])
else
(if i.val < 230 then
![354, 453, 40, 454, 455]
else
![355, 420, 451, 102, 456]))
else
(if i.val < 233 then
(if i.val < 232 then
![356, 421, 455, 456, 102]
else
![357, 42, 457, 364, 458])
else
(if i.val < 234 then
![358, 188, 447, 459, 460]
else
![359, 458, 460, 366, 104])))
else
(if i.val < 239 then
(if i.val < 237 then
(if i.val < 236 then
![360, 461, 438, 462, 463]
else
![361, 462, 454, 105, 464])
else
(if i.val < 238 then
![362, 463, 43, 464, 105]
else
![363, 366, 456, 107, 106]))
else
(if i.val < 241 then
(if i.val < 240 then
![364, 298, 465, 466, 467]
else
![365, 430, 44, 468, 469])
else
(if i.val < 242 then
![104, 466, 470, 108, 471]
else
![366, 467, 469, 471, 108]))))))))
else
(if i.val < 364 then
(if i.val < 303 then
(if i.val < 273 then
(if i.val < 258 then
(if i.val < 250 then
(if i.val < 246 then
(if i.val < 244 then
![367, 433, 472, 473, 474]
else
(if i.val < 245 then
![368, 52, 474, 110, 109]
else
![369, 45, 475, 476, 477]))
else
(if i.val < 248 then
(if i.val < 247 then
![370, 436, 478, 479, 480]
else
![371, 476, 158, 111, 481])
else
(if i.val < 249 then
![372, 477, 480, 481, 111]
else
![373, 438, 482, 112, 483])))
else
(if i.val < 254 then
(if i.val < 252 then
(if i.val < 251 then
![374, 439, 47, 483, 112]
else
![375, 470, 484, 485, 486])
else
(if i.val < 253 then
![376, 481, 486, 114, 113]
else
![377, 160, 46, 487, 488]))
else
(if i.val < 256 then
(if i.val < 255 then
![378, 380, 485, 115, 489]
else
![379, 442, 488, 489, 115])
else
(if i.val < 257 then
![380, 443, 490, 491, 492]
else
![381, 49, 493, 117, 494]))))
else
(if i.val < 265 then
(if i.val < 261 then
(if i.val < 259 then
![382, 50, 492, 494, 117]
else
(if i.val < 260 then
![383, 478, 48, 495, 496]
else
![384, 447, 53, 118, 497]))
else
(if i.val < 263 then
(if i.val < 262 then
![385, 448, 496, 497, 118]
else
![386, 158, 498, 326, 499])
else
(if i.val < 264 then
![387, 494, 499, 120, 119]
else
![388, 450, 49, 500, 501])))
else
(if i.val < 269 then
(if i.val < 267 then
(if i.val < 266 then
![389, 485, 55, 121, 502]
else
![390, 486, 501, 502, 121])
else
(if i.val < 268 then
![391, 503, 495, 504, 505]
else
![217, 504, 500, 123, 506]))
else
(if i.val < 271 then
(if i.val < 270 then
![392, 505, 52, 506, 123]
else
![393, 456, 502, 125, 124])
else
(if i.val < 272 then
![97, 507, 491, 137, 508]
else
![394, 55, 509, 126, 510])))))
else
(if i.val < 288 then
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
![395, 56, 508, 510, 126]
else
(if i.val < 275 then
![396, 511, 479, 512, 513]
else
![397, 512, 504, 127, 514]))
else
(if i.val < 278 then
(if i.val < 277 then
![398, 513, 497, 514, 127]
else
![399, 365, 326, 515, 516])
else
(if i.val < 279 then
![400, 510, 516, 129, 128]
else
![401, 54, 468, 517, 518])))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
![402, 517, 487, 130, 519]
else
![403, 518, 483, 519, 130])
else
(if i.val < 283 then
![404, 519, 506, 132, 131]
else
![89, 520, 521, 457, 522]))
else
(if i.val < 286 then
(if i.val < 285 then
![90, 523, 57, 524, 525]
else
![91, 457, 526, 134, 527])
else
(if i.val < 287 then
![92, 522, 525, 527, 134]
else
![93, 431, 528, 529, 530]))))
else
(if i.val < 295 then
(if i.val < 291 then
(if i.val < 289 then
![94, 66, 530, 136, 135]
else
(if i.val < 290 then
![95, 58, 531, 507, 532]
else
![96, 268, 533, 503, 534]))
else
(if i.val < 293 then
(if i.val < 292 then
![98, 532, 534, 508, 137]
else
![99, 535, 536, 472, 537])
else
(if i.val < 294 then
![100, 472, 538, 138, 539]
else
![101, 537, 60, 539, 138])))
else
(if i.val < 299 then
(if i.val < 297 then
(if i.val < 296 then
![102, 526, 540, 541, 542]
else
![103, 508, 542, 140, 139])
else
(if i.val < 298 then
![105, 493, 59, 543, 544]
else
![106, 108, 541, 141, 545]))
else
(if i.val < 301 then
(if i.val < 300 then
![107, 471, 544, 545, 141]
else
![108, 546, 547, 171, 548])
else
(if i.val < 302 then
![109, 63, 549, 143, 550]
else
![110, 64, 548, 550, 143]))))))
else
(if i.val < 333 then
(if i.val < 318 then
(if i.val < 310 then
(if i.val < 306 then
(if i.val < 304 then
![111, 551, 552, 419, 553]
else
(if i.val < 305 then
![112, 533, 61, 554, 555]
else
![113, 419, 556, 144, 557]))
else
(if i.val < 308 then
(if i.val < 307 then
![114, 553, 555, 557, 144]
else
![115, 491, 422, 558, 559])
else
(if i.val < 309 then
![116, 550, 559, 146, 145]
else
![117, 62, 560, 561, 562])))
else
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
![118, 536, 563, 564, 565]
else
![119, 561, 405, 147, 566])
else
(if i.val < 313 then
![120, 562, 565, 566, 147]
else
![121, 556, 567, 568, 569]))
else
(if i.val < 316 then
(if i.val < 315 then
![122, 566, 569, 149, 148]
else
![123, 570, 63, 342, 571])
else
(if i.val < 317 then
![124, 541, 568, 150, 572]
else
![125, 542, 571, 572, 150]))))
else
(if i.val < 325 then
(if i.val < 321 then
(if i.val < 319 then
![126, 65, 164, 573, 574]
else
(if i.val < 320 then
![127, 417, 564, 575, 576]
else
![128, 573, 577, 152, 578]))
else
(if i.val < 323 then
(if i.val < 322 then
![129, 574, 576, 578, 152]
else
![130, 579, 554, 580, 581])
else
(if i.val < 324 then
![131, 580, 342, 153, 582]
else
![132, 581, 66, 582, 153])))
else
(if i.val < 329 then
(if i.val < 327 then
(if i.val < 326 then
![133, 578, 572, 155, 154]
else
![520, 67, 128, 262, 583])
else
(if i.val < 328 then
![521, 584, 585, 586, 587]
else
![457, 262, 588, 156, 589]))
else
(if i.val < 331 then
(if i.val < 330 then
![522, 583, 587, 589, 156]
else
![523, 590, 591, 592, 593])
else
(if i.val < 332 then
![524, 592, 274, 157, 594]
else
![525, 593, 69, 594, 157])))))
else
(if i.val < 348 then
(if i.val < 340 then
(if i.val < 336 then
(if i.val < 334 then
![526, 83, 247, 595, 596]
else
(if i.val < 335 then
![527, 589, 596, 159, 158]
else
![431, 253, 597, 531, 598]))
else
(if i.val < 338 then
(if i.val < 337 then
![528, 599, 68, 478, 600]
else
![529, 531, 595, 160, 601])
else
(if i.val < 339 then
![530, 598, 600, 601, 160]
else
![531, 602, 603, 210, 604])))
else
(if i.val < 344 then
(if i.val < 342 then
(if i.val < 341 then
![507, 72, 605, 162, 606]
else
![532, 73, 604, 606, 162])
else
(if i.val < 343 then
![268, 607, 608, 315, 609]
else
![533, 585, 70, 610, 611]))
else
(if i.val < 346 then
(if i.val < 345 then
![503, 315, 612, 163, 613]
else
![534, 609, 611, 613, 163])
else
(if i.val < 347 then
![491, 588, 318, 560, 614]
else
![508, 606, 614, 165, 164]))))
else
(if i.val < 356 then
(if i.val < 352 then
(if i.val < 350 then
(if i.val < 349 then
![535, 71, 615, 616, 617]
else
![536, 591, 618, 619, 620])
else
(if i.val < 351 then
![472, 616, 301, 166, 621]
else
![537, 617, 620, 621, 166]))
else
(if i.val < 354 then
(if i.val < 353 then
![538, 612, 622, 623, 624]
else
![539, 621, 624, 168, 167])
else
(if i.val < 355 then
![540, 625, 72, 407, 626]
else
![541, 595, 623, 169, 627])))
else
(if i.val < 360 then
(if i.val < 358 then
(if i.val < 357 then
![542, 596, 626, 627, 169]
else
![466, 74, 203, 546, 628])
else
(if i.val < 359 then
![470, 313, 619, 629, 630]
else
![471, 628, 630, 548, 171]))
else
(if i.val < 362 then
(if i.val < 361 then
![493, 631, 610, 632, 633]
else
![543, 632, 407, 172, 634])
else
(if i.val < 363 then
![544, 633, 75, 634, 172]
else
![545, 548, 627, 174, 173])))))))
else
(if i.val < 425 then
(if i.val < 394 then
(if i.val < 379 then
(if i.val < 371 then
(if i.val < 367 then
(if i.val < 365 then
![546, 106, 635, 232, 636]
else
(if i.val < 366 then
![547, 603, 76, 637, 638]
else
![548, 636, 638, 234, 175]))
else
(if i.val < 369 then
(if i.val < 368 then
![549, 605, 225, 639, 640]
else
![550, 84, 640, 177, 176])
else
(if i.val < 370 then
![551, 77, 641, 642, 643]
else
![552, 608, 644, 645, 646])))
else
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
![419, 642, 285, 178, 647]
else
![553, 643, 646, 647, 178])
else
(if i.val < 374 then
![554, 610, 648, 179, 649]
else
![555, 611, 79, 649, 179]))
else
(if i.val < 377 then
(if i.val < 376 then
![556, 233, 650, 651, 652]
else
![557, 647, 652, 181, 180])
else
(if i.val < 378 then
![422, 287, 78, 429, 653]
else
![558, 560, 651, 182, 654]))))
else
(if i.val < 386 then
(if i.val < 382 then
(if i.val < 380 then
![559, 614, 653, 654, 182]
else
(if i.val < 381 then
![560, 615, 655, 221, 656]
else
![561, 81, 235, 184, 657]))
else
(if i.val < 384 then
(if i.val < 383 then
![562, 82, 656, 657, 184]
else
![563, 644, 80, 658, 659])
else
(if i.val < 385 then
![564, 619, 85, 185, 660]
else
![565, 620, 659, 660, 185])))
else
(if i.val < 390 then
(if i.val < 388 then
(if i.val < 387 then
![405, 285, 661, 520, 662]
else
![566, 657, 662, 187, 186])
else
(if i.val < 389 then
![567, 622, 81, 436, 663]
else
![568, 651, 87, 188, 664]))
else
(if i.val < 392 then
(if i.val < 391 then
![569, 652, 663, 664, 188]
else
![570, 219, 658, 435, 665])
else
(if i.val < 393 then
![571, 665, 84, 437, 190]
else
![572, 627, 664, 192, 191])))))
else
(if i.val < 409 then
(if i.val < 401 then
(if i.val < 397 then
(if i.val < 395 then
![573, 87, 666, 193, 667]
else
(if i.val < 396 then
![574, 88, 222, 667, 193]
else
![417, 668, 645, 669, 670]))
else
(if i.val < 399 then
(if i.val < 398 then
![575, 669, 435, 194, 671]
else
![576, 670, 660, 671, 194])
else
(if i.val < 400 then
![577, 547, 520, 672, 673]
else
![578, 667, 673, 196, 195])))
else
(if i.val < 405 then
(if i.val < 403 then
(if i.val < 402 then
![579, 86, 637, 446, 674]
else
![580, 446, 429, 197, 675])
else
(if i.val < 404 then
![581, 674, 649, 675, 197]
else
![582, 675, 437, 199, 198]))
else
(if i.val < 407 then
(if i.val < 406 then
![262, 91, 676, 201, 677]
else
![583, 92, 578, 677, 201])
else
(if i.val < 408 then
![584, 678, 679, 354, 680]
else
![585, 112, 89, 681, 682]))))
else
(if i.val < 417 then
(if i.val < 413 then
(if i.val < 411 then
(if i.val < 410 then
![586, 354, 683, 202, 684]
else
![587, 680, 682, 684, 202])
else
(if i.val < 412 then
![588, 115, 357, 615, 685]
else
![589, 677, 685, 204, 203]))
else
(if i.val < 415 then
(if i.val < 414 then
![590, 90, 558, 686, 687]
else
![591, 118, 688, 689, 690])
else
(if i.val < 416 then
![592, 686, 340, 205, 691]
else
![593, 687, 690, 691, 205])))
else
(if i.val < 421 then
(if i.val < 419 then
(if i.val < 418 then
![274, 683, 692, 693, 694]
else
![594, 691, 694, 207, 206])
else
(if i.val < 420 then
![247, 695, 91, 303, 696]
else
![595, 124, 693, 208, 697]))
else
(if i.val < 423 then
(if i.val < 422 then
![596, 125, 696, 697, 208]
else
![253, 93, 145, 602, 698])
else
(if i.val < 424 then
![597, 352, 689, 699, 700]
else
![598, 698, 700, 604, 210]))))))
else
(if i.val < 455 then
(if i.val < 440 then
(if i.val < 432 then
(if i.val < 428 then
(if i.val < 426 then
![599, 701, 681, 702, 703]
else
(if i.val < 427 then
![478, 702, 303, 211, 704]
else
![600, 703, 94, 704, 211]))
else
(if i.val < 430 then
(if i.val < 429 then
![601, 604, 697, 213, 212]
else
![602, 529, 705, 377, 706])
else
(if i.val < 431 then
![603, 577, 95, 707, 708]
else
![210, 377, 709, 214, 710])))
else
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![604, 706, 708, 710, 214]
else
![605, 676, 711, 641, 712])
else
(if i.val < 435 then
![606, 103, 712, 216, 215]
else
![607, 96, 713, 391, 714]))
else
(if i.val < 438 then
(if i.val < 437 then
![608, 679, 198, 388, 715]
else
![609, 714, 715, 392, 217])
else
(if i.val < 439 then
![610, 681, 381, 218, 716]
else
![611, 682, 98, 716, 218]))))
else
(if i.val < 447 then
(if i.val < 443 then
(if i.val < 441 then
![612, 709, 717, 655, 718]
else
(if i.val < 442 then
![613, 392, 718, 220, 219]
else
![614, 685, 395, 656, 221]))
else
(if i.val < 445 then
(if i.val < 444 then
![615, 558, 719, 720, 721]
else
![616, 100, 722, 223, 723])
else
(if i.val < 446 then
![617, 101, 721, 723, 223]
else
![618, 198, 99, 401, 724])))
else
(if i.val < 451 then
(if i.val < 449 then
(if i.val < 448 then
![619, 689, 104, 224, 725]
else
![620, 690, 724, 725, 224])
else
(if i.val < 450 then
![621, 723, 368, 226, 225]
else
![622, 692, 100, 726, 727]))
else
(if i.val < 453 then
(if i.val < 452 then
![623, 655, 106, 227, 728]
else
![624, 718, 727, 728, 227])
else
(if i.val < 454 then
![625, 729, 401, 730, 731]
else
![407, 730, 726, 229, 732])))))
else
(if i.val < 470 then
(if i.val < 462 then
(if i.val < 458 then
(if i.val < 456 then
![626, 731, 103, 732, 229]
else
(if i.val < 457 then
![627, 697, 728, 231, 230]
else
![203, 386, 720, 283, 733]))
else
(if i.val < 460 then
(if i.val < 459 then
![628, 107, 733, 636, 232]
else
![629, 389, 730, 233, 734])
else
(if i.val < 461 then
![630, 390, 725, 734, 233]
else
![631, 105, 707, 735, 736])))
else
(if i.val < 466 then
(if i.val < 464 then
(if i.val < 463 then
![632, 735, 394, 235, 737]
else
![633, 736, 716, 737, 235])
else
(if i.val < 465 then
![634, 737, 732, 237, 236]
else
![635, 705, 738, 739, 740]))
else
(if i.val < 468 then
(if i.val < 467 then
![232, 141, 328, 239, 741]
else
![636, 545, 740, 741, 239])
else
(if i.val < 469 then
![637, 707, 742, 240, 743]
else
![638, 708, 110, 743, 240]))))
else
(if i.val < 478 then
(if i.val < 474 then
(if i.val < 472 then
(if i.val < 471 then
![233, 121, 744, 745, 746]
else
![234, 741, 746, 242, 241])
else
(if i.val < 473 then
![225, 747, 109, 292, 748]
else
![639, 641, 745, 243, 749]))
else
(if i.val < 476 then
(if i.val < 475 then
![640, 712, 748, 749, 243]
else
![641, 713, 750, 751, 752])
else
(if i.val < 477 then
![642, 113, 753, 245, 754]
else
![643, 114, 752, 754, 245])))
else
(if i.val < 482 then
(if i.val < 480 then
(if i.val < 479 then
![644, 738, 111, 336, 755]
else
![645, 388, 331, 246, 756])
else
(if i.val < 481 then
![646, 715, 755, 756, 246]
else
![647, 754, 334, 248, 247]))
else
(if i.val < 484 then
(if i.val < 483 then
![648, 331, 130, 590, 757]
else
![649, 716, 757, 250, 249])
else
(if i.val < 485 then
![650, 717, 113, 758, 759]
else
![651, 745, 590, 251, 760])))))))))
else
(if i.val < 729 then
(if i.val < 607 then
(if i.val < 546 then
(if i.val < 516 then
(if i.val < 501 then
(if i.val < 493 then
(if i.val < 489 then
(if i.val < 487 then
![652, 746, 759, 760, 251]
else
(if i.val < 488 then
![429, 337, 758, 253, 761]
else
![653, 338, 116, 761, 253]))
else
(if i.val < 491 then
(if i.val < 490 then
![654, 656, 760, 255, 254]
else
![655, 750, 117, 762, 763])
else
(if i.val < 492 then
![221, 720, 126, 256, 764]
else
![656, 721, 763, 764, 256])))
else
(if i.val < 497 then
(if i.val < 495 then
(if i.val < 494 then
![235, 753, 765, 766, 767]
else
![657, 122, 767, 258, 257])
else
(if i.val < 496 then
![658, 336, 515, 259, 768]
else
![659, 755, 120, 768, 259]))
else
(if i.val < 499 then
(if i.val < 498 then
![660, 725, 129, 261, 260]
else
![661, 367, 119, 769, 770])
else
(if i.val < 500 then
![662, 334, 770, 583, 262]
else
![436, 726, 131, 264, 771]))))
else
(if i.val < 508 then
(if i.val < 504 then
(if i.val < 502 then
![663, 727, 122, 771, 264]
else
(if i.val < 503 then
![664, 760, 133, 266, 265]
else
![219, 123, 762, 290, 772]))
else
(if i.val < 506 then
(if i.val < 505 then
![435, 290, 769, 267, 773]
else
![665, 772, 768, 773, 267])
else
(if i.val < 507 then
![437, 773, 771, 269, 268]
else
![215, 139, 751, 289, 774])))
else
(if i.val < 512 then
(if i.val < 510 then
(if i.val < 509 then
![222, 774, 764, 291, 271]
else
![666, 635, 766, 775, 776])
else
(if i.val < 511 then
![667, 133, 776, 273, 272]
else
![668, 127, 739, 777, 778]))
else
(if i.val < 514 then
(if i.val < 513 then
![669, 777, 337, 274, 779]
else
![670, 778, 756, 779, 274])
else
(if i.val < 515 then
![671, 779, 773, 276, 275]
else
![672, 637, 267, 277, 780])))))
else
(if i.val < 531 then
(if i.val < 523 then
(if i.val < 519 then
(if i.val < 517 then
![673, 638, 583, 780, 277]
else
(if i.val < 518 then
![446, 131, 292, 279, 781]
else
![674, 132, 743, 781, 279]))
else
(if i.val < 521 then
(if i.val < 520 then
![675, 781, 761, 281, 280]
else
![201, 134, 195, 386, 782])
else
(if i.val < 522 then
![202, 454, 783, 729, 784]
else
![204, 782, 784, 733, 283])))
else
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
![205, 785, 786, 711, 787]
else
![206, 711, 396, 284, 788])
else
(if i.val < 526 then
![207, 787, 136, 788, 284]
else
![208, 150, 371, 789, 790]))
else
(if i.val < 529 then
(if i.val < 528 then
![209, 733, 790, 286, 285]
else
![211, 722, 135, 644, 791])
else
(if i.val < 530 then
![212, 214, 789, 287, 792]
else
![213, 710, 791, 792, 287]))))
else
(if i.val < 538 then
(if i.val < 534 then
(if i.val < 532 then
![214, 487, 793, 335, 794]
else
(if i.val < 533 then
![216, 140, 794, 774, 289]
else
![218, 783, 137, 765, 795]))
else
(if i.val < 536 then
(if i.val < 535 then
![220, 506, 795, 772, 290]
else
![223, 138, 796, 747, 797])
else
(if i.val < 537 then
![224, 786, 517, 744, 798]
else
![226, 797, 798, 748, 292])))
else
(if i.val < 542 then
(if i.val < 540 then
(if i.val < 539 then
![227, 762, 799, 800, 801]
else
![228, 748, 801, 294, 293])
else
(if i.val < 541 then
![229, 742, 139, 584, 802]
else
![230, 789, 800, 295, 803]))
else
(if i.val < 544 then
(if i.val < 543 then
![231, 790, 802, 803, 295]
else
![236, 766, 584, 297, 804])
else
(if i.val < 545 then
![237, 767, 142, 804, 297]
else
![238, 242, 803, 299, 298]))))))
else
(if i.val < 576 then
(if i.val < 561 then
(if i.val < 553 then
(if i.val < 549 then
(if i.val < 547 then
![239, 173, 805, 357, 806]
else
(if i.val < 548 then
![240, 793, 143, 807, 808]
else
![242, 806, 808, 359, 300]))
else
(if i.val < 551 then
(if i.val < 550 then
![243, 751, 350, 809, 810]
else
![244, 151, 810, 302, 301])
else
(if i.val < 552 then
![245, 144, 811, 695, 812]
else
![246, 500, 426, 692, 813])))
else
(if i.val < 557 then
(if i.val < 555 then
(if i.val < 554 then
![248, 812, 813, 696, 303]
else
![249, 765, 686, 304, 814])
else
(if i.val < 556 then
![250, 795, 146, 814, 304]
else
![251, 358, 815, 816, 817]))
else
(if i.val < 559 then
(if i.val < 558 then
![252, 696, 817, 306, 305]
else
![254, 256, 816, 307, 818])
else
(if i.val < 560 then
![255, 764, 698, 818, 307]
else
![256, 796, 819, 346, 820]))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
![257, 148, 360, 309, 821]
else
(if i.val < 563 then
![258, 149, 820, 821, 309]
else
![259, 426, 147, 701, 822]))
else
(if i.val < 566 then
(if i.val < 565 then
![260, 744, 152, 310, 823]
else
![261, 798, 822, 823, 310])
else
(if i.val < 567 then
![263, 821, 677, 312, 311]
else
![264, 799, 148, 608, 824])))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
![265, 816, 154, 313, 825]
else
![266, 817, 824, 825, 313])
else
(if i.val < 571 then
![267, 344, 701, 607, 826]
else
![269, 826, 151, 609, 315]))
else
(if i.val < 574 then
(if i.val < 573 then
![270, 803, 825, 317, 316]
else
![272, 154, 827, 318, 828])
else
(if i.val < 575 then
![273, 155, 347, 828, 318]
else
![275, 693, 607, 319, 829])))))
else
(if i.val < 591 then
(if i.val < 583 then
(if i.val < 579 then
(if i.val < 577 then
![276, 694, 823, 829, 319]
else
(if i.val < 578 then
![277, 240, 201, 830, 831]
else
![278, 828, 831, 321, 320]))
else
(if i.val < 581 then
(if i.val < 580 then
![279, 153, 807, 618, 832]
else
![280, 618, 602, 322, 833])
else
(if i.val < 582 then
![281, 832, 814, 833, 322]
else
![282, 833, 609, 324, 323])))
else
(if i.val < 587 then
(if i.val < 585 then
(if i.val < 584 then
![782, 159, 278, 499, 326]
else
![454, 834, 835, 540, 836])
else
(if i.val < 586 then
![783, 179, 156, 837, 838]
else
![729, 540, 511, 327, 839]))
else
(if i.val < 589 then
(if i.val < 588 then
![784, 836, 838, 839, 327]
else
![720, 182, 466, 796, 840])
else
(if i.val < 590 then
![733, 499, 840, 329, 328]
else
![785, 157, 254, 482, 841]))))
else
(if i.val < 599 then
(if i.val < 595 then
(if i.val < 593 then
(if i.val < 592 then
![786, 185, 842, 843, 844]
else
![711, 482, 507, 330, 845])
else
(if i.val < 594 then
![787, 841, 844, 845, 330]
else
![788, 845, 513, 332, 331]))
else
(if i.val < 597 then
(if i.val < 596 then
![789, 191, 512, 333, 846]
else
![790, 192, 481, 846, 333])
else
(if i.val < 598 then
![709, 538, 843, 750, 847]
else
![710, 488, 847, 794, 335])))
else
(if i.val < 603 then
(if i.val < 601 then
(if i.val < 600 then
![722, 495, 837, 738, 848]
else
![791, 848, 161, 755, 336])
else
(if i.val < 602 then
![792, 794, 846, 338, 337]
else
![487, 212, 849, 422, 850]))
else
(if i.val < 605 then
(if i.val < 604 then
![793, 277, 162, 851, 852]
else
![794, 850, 852, 424, 339])
else
(if i.val < 606 then
![751, 498, 415, 811, 853]
else
![774, 170, 853, 341, 340])))))))
else
(if i.val < 668 then
(if i.val < 637 then
(if i.val < 622 then
(if i.val < 614 then
(if i.val < 610 then
(if i.val < 608 then
![504, 163, 854, 570, 855]
else
(if i.val < 609 then
![500, 835, 323, 567, 856]
else
![506, 855, 856, 571, 342]))
else
(if i.val < 612 then
(if i.val < 611 then
![765, 837, 561, 343, 857]
else
![795, 838, 165, 857, 343])
else
(if i.val < 613 then
![762, 423, 858, 819, 859]
else
![772, 571, 859, 345, 344])))
else
(if i.val < 618 then
(if i.val < 616 then
(if i.val < 615 then
![764, 840, 574, 820, 346]
else
![796, 254, 860, 411, 861])
else
(if i.val < 617 then
![747, 167, 425, 348, 862]
else
![797, 168, 861, 862, 348]))
else
(if i.val < 620 then
(if i.val < 619 then
![517, 323, 166, 579, 863]
else
![744, 843, 171, 349, 864])
else
(if i.val < 621 then
![798, 844, 863, 864, 349]
else
![748, 862, 550, 351, 350]))))
else
(if i.val < 629 then
(if i.val < 625 then
(if i.val < 623 then
![799, 479, 167, 679, 865]
else
(if i.val < 624 then
![800, 819, 173, 352, 866]
else
![801, 859, 865, 866, 352]))
else
(if i.val < 627 then
(if i.val < 626 then
![742, 409, 579, 678, 867]
else
![802, 867, 170, 680, 354])
else
(if i.val < 628 then
![803, 846, 866, 356, 355]
else
![741, 174, 412, 806, 357])))
else
(if i.val < 633 then
(if i.val < 631 then
(if i.val < 630 then
![745, 568, 678, 358, 868]
else
![746, 569, 864, 868, 358])
else
(if i.val < 632 then
![753, 172, 851, 688, 869]
else
![766, 688, 573, 360, 870]))
else
(if i.val < 635 then
(if i.val < 634 then
![767, 869, 857, 870, 360]
else
![804, 870, 680, 362, 361])
else
(if i.val < 636 then
![805, 849, 871, 872, 873]
else
![806, 238, 873, 458, 364])))))
else
(if i.val < 652 then
(if i.val < 644 then
(if i.val < 640 then
(if i.val < 638 then
![807, 851, 453, 365, 874]
else
(if i.val < 639 then
![808, 852, 177, 874, 365]
else
![809, 811, 459, 367, 875]))
else
(if i.val < 642 then
(if i.val < 641 then
![810, 853, 449, 875, 367]
else
![811, 854, 876, 433, 877])
else
(if i.val < 643 then
![695, 180, 461, 369, 878]
else
![812, 181, 877, 878, 369])))
else
(if i.val < 648 then
(if i.val < 646 then
(if i.val < 645 then
![426, 871, 178, 528, 879]
else
![692, 567, 524, 370, 880])
else
(if i.val < 647 then
![813, 856, 879, 880, 370]
else
![696, 878, 527, 372, 371]))
else
(if i.val < 650 then
(if i.val < 649 then
![686, 524, 197, 785, 881]
else
![814, 857, 881, 374, 373])
else
(if i.val < 651 then
![815, 858, 180, 705, 882]
else
![816, 459, 785, 375, 883]))))
else
(if i.val < 660 then
(if i.val < 656 then
(if i.val < 654 then
(if i.val < 653 then
![817, 460, 882, 883, 375]
else
![698, 530, 183, 706, 377])
else
(if i.val < 655 then
![818, 820, 883, 379, 378]
else
![819, 876, 184, 440, 884]))
else
(if i.val < 658 then
(if i.val < 657 then
![820, 861, 884, 442, 380]
else
![821, 189, 463, 382, 381])
else
(if i.val < 659 then
![701, 528, 672, 383, 885]
else
![822, 879, 187, 885, 383])))
else
(if i.val < 664 then
(if i.val < 662 then
(if i.val < 661 then
![823, 864, 196, 385, 384]
else
![676, 549, 186, 713, 886])
else
(if i.val < 663 then
![677, 527, 886, 782, 386]
else
![824, 865, 189, 715, 388]))
else
(if i.val < 666 then
(if i.val < 665 then
![825, 883, 200, 390, 389]
else
![826, 441, 885, 714, 391])
else
(if i.val < 667 then
![827, 805, 462, 717, 887]
else
![828, 200, 887, 395, 394]))))))
else
(if i.val < 698 then
(if i.val < 683 then
(if i.val < 675 then
(if i.val < 671 then
(if i.val < 669 then
![683, 194, 872, 719, 888]
else
(if i.val < 670 then
![693, 719, 529, 396, 889]
else
![694, 888, 880, 889, 396]))
else
(if i.val < 673 then
(if i.val < 672 then
![829, 889, 714, 398, 397]
else
![830, 807, 391, 399, 890])
else
(if i.val < 674 then
![831, 808, 782, 890, 399]
else
![832, 199, 874, 724, 401])))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
![833, 724, 706, 403, 402]
else
![498, 243, 311, 854, 891])
else
(if i.val < 678 then
![499, 209, 891, 406, 405]
else
![834, 202, 809, 625, 892]))
else
(if i.val < 681 then
(if i.val < 680 then
![835, 246, 361, 622, 893]
else
![836, 892, 893, 626, 407])
else
(if i.val < 682 then
![837, 249, 616, 408, 894]
else
![838, 250, 204, 894, 408]))))
else
(if i.val < 690 then
(if i.val < 686 then
(if i.val < 684 then
![511, 319, 895, 860, 896]
else
(if i.val < 685 then
![839, 626, 896, 410, 409]
else
![840, 255, 628, 861, 411]))
else
(if i.val < 688 then
(if i.val < 687 then
![482, 206, 322, 413, 897]
else
![841, 207, 818, 897, 413])
else
(if i.val < 689 then
![842, 361, 205, 631, 898]
else
![843, 260, 210, 414, 899])))
else
(if i.val < 694 then
(if i.val < 692 then
(if i.val < 691 then
![844, 261, 898, 899, 414]
else
![845, 897, 606, 416, 415])
else
(if i.val < 693 then
![479, 264, 206, 552, 900]
else
![512, 860, 212, 417, 901]))
else
(if i.val < 696 then
(if i.val < 695 then
![513, 896, 900, 901, 417]
else
![476, 305, 631, 551, 902])
else
(if i.val < 697 then
![481, 902, 209, 553, 419]
else
![846, 270, 901, 421, 420])))))
else
(if i.val < 713 then
(if i.val < 705 then
(if i.val < 701 then
(if i.val < 699 then
![488, 213, 308, 850, 422]
else
(if i.val < 700 then
![750, 623, 551, 423, 903]
else
![847, 624, 899, 903, 423]))
else
(if i.val < 703 then
(if i.val < 702 then
![495, 211, 830, 563, 904]
else
![738, 563, 546, 425, 905])
else
(if i.val < 704 then
![848, 904, 894, 905, 425]
else
![755, 905, 553, 427, 426])))
else
(if i.val < 709 then
(if i.val < 707 then
(if i.val < 706 then
![849, 827, 402, 650, 906]
else
![850, 792, 906, 653, 429])
else
(if i.val < 708 then
![851, 830, 642, 430, 907]
else
![852, 831, 216, 907, 430]))
else
(if i.val < 711 then
(if i.val < 710 then
![423, 227, 908, 876, 909]
else
![424, 653, 909, 432, 431])
else
(if i.val < 712 then
![415, 648, 215, 523, 910]
else
![853, 891, 910, 877, 433]))))
else
(if i.val < 721 then
(if i.val < 717 then
(if i.val < 715 then
(if i.val < 714 then
![854, 809, 397, 661, 911]
else
![855, 220, 911, 665, 435])
else
(if i.val < 716 then
![856, 893, 404, 663, 436]
else
![857, 894, 657, 439, 438]))
else
(if i.val < 719 then
(if i.val < 718 then
![858, 895, 219, 666, 912]
else
![859, 909, 912, 884, 440])
else
(if i.val < 720 then
![860, 397, 223, 668, 913]
else
![411, 307, 232, 443, 914])))
else
(if i.val < 725 then
(if i.val < 723 then
(if i.val < 722 then
![861, 818, 913, 914, 443]
else
![425, 658, 915, 871, 916])
else
(if i.val < 724 then
![862, 228, 916, 445, 444]
else
![863, 404, 226, 674, 446]))
else
(if i.val < 727 then
(if i.val < 726 then
![864, 899, 234, 448, 447]
else
![679, 552, 236, 450, 917])
else
(if i.val < 728 then
![865, 900, 228, 917, 450]
else
![866, 884, 238, 452, 451]))))))))
else
(if i.val < 850 then
(if i.val < 789 then
(if i.val < 759 then
(if i.val < 744 then
(if i.val < 736 then
(if i.val < 732 then
(if i.val < 730 then
![409, 229, 668, 521, 918]
else
(if i.val < 731 then
![678, 521, 639, 453, 919]
else
![867, 918, 674, 919, 453]))
else
(if i.val < 734 then
(if i.val < 733 then
![680, 919, 917, 455, 454]
else
![412, 662, 914, 522, 457])
else
(if i.val < 735 then
![868, 664, 919, 460, 459]
else
![688, 236, 523, 461, 920])))
else
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
![869, 237, 907, 920, 461]
else
![870, 920, 667, 463, 462])
else
(if i.val < 739 then
![871, 259, 239, 599, 921]
else
![872, 650, 586, 465, 922]))
else
(if i.val < 742 then
(if i.val < 741 then
![873, 906, 921, 922, 465]
else
![458, 299, 589, 467, 466])
else
(if i.val < 743 then
![453, 586, 279, 834, 923]
else
![874, 907, 923, 469, 468]))))
else
(if i.val < 751 then
(if i.val < 747 then
(if i.val < 745 then
![447, 908, 241, 536, 924]
else
(if i.val < 746 then
![459, 265, 834, 470, 925]
else
![460, 266, 924, 925, 470]))
else
(if i.val < 749 then
(if i.val < 748 then
![444, 293, 599, 535, 926]
else
![449, 926, 244, 537, 472])
else
(if i.val < 750 then
![875, 877, 925, 474, 473]
else
![876, 800, 245, 597, 927])))
else
(if i.val < 755 then
(if i.val < 753 then
(if i.val < 752 then
![433, 661, 592, 475, 928]
else
![877, 911, 927, 928, 475])
else
(if i.val < 754 then
![461, 297, 929, 842, 930]
else
![878, 252, 930, 477, 476]))
else
(if i.val < 757 then
(if i.val < 756 then
![879, 921, 248, 600, 478]
else
![880, 663, 594, 480, 479])
else
(if i.val < 758 then
![881, 594, 281, 841, 482]
else
![705, 666, 280, 484, 931])))))
else
(if i.val < 774 then
(if i.val < 766 then
(if i.val < 762 then
(if i.val < 760 then
![882, 912, 252, 931, 484]
else
(if i.val < 761 then
![883, 925, 841, 486, 485]
else
![706, 601, 931, 488, 487]))
else
(if i.val < 764 then
(if i.val < 763 then
![440, 597, 775, 490, 932]
else
![884, 927, 258, 932, 490])
else
(if i.val < 765 then
![442, 914, 273, 492, 491]
else
![438, 915, 257, 533, 933])))
else
(if i.val < 770 then
(if i.val < 768 then
(if i.val < 767 then
![462, 842, 272, 493, 934]
else
![463, 930, 933, 934, 493])
else
(if i.val < 769 then
![885, 600, 780, 496, 495]
else
![713, 639, 275, 498, 935]))
else
(if i.val < 772 then
(if i.val < 771 then
![886, 640, 263, 935, 498]
else
![715, 917, 282, 501, 500])
else
(if i.val < 773 then
![441, 269, 932, 534, 503]
else
![714, 534, 935, 505, 504]))))
else
(if i.val < 781 then
(if i.val < 777 then
(if i.val < 775 then
![434, 296, 928, 532, 507]
else
(if i.val < 776 then
![717, 872, 503, 509, 936]
else
![887, 873, 934, 936, 509]))
else
(if i.val < 779 then
(if i.val < 778 then
![719, 275, 535, 511, 937]
else
![888, 276, 922, 937, 511])
else
(if i.val < 780 then
![889, 937, 601, 513, 512]
else
![890, 874, 505, 516, 515])))
else
(if i.val < 785 then
(if i.val < 783 then
(if i.val < 782 then
![724, 282, 537, 518, 517]
else
![406, 286, 400, 662, 520])
else
(if i.val < 784 then
![408, 304, 283, 915, 938]
else
![410, 732, 938, 918, 521]))
else
(if i.val < 787 then
(if i.val < 786 then
![413, 284, 378, 648, 939]
else
![414, 310, 735, 908, 940])
else
(if i.val < 788 then
![416, 939, 940, 910, 523]
else
![418, 910, 670, 525, 524]))))))
else
(if i.val < 819 then
(if i.val < 804 then
(if i.val < 796 then
(if i.val < 792 then
(if i.val < 790 then
![420, 316, 669, 526, 941]
else
(if i.val < 791 then
![421, 317, 647, 941, 526]
else
![427, 916, 288, 879, 528]))
else
(if i.val < 794 then
(if i.val < 793 then
![428, 432, 941, 530, 529]
else
![430, 399, 289, 929, 942])
else
(if i.val < 795 then
![432, 761, 942, 598, 531]
else
![439, 938, 291, 933, 533])))
else
(if i.val < 800 then
(if i.val < 798 then
(if i.val < 797 then
![443, 378, 777, 588, 943]
else
![445, 294, 943, 926, 535])
else
(if i.val < 799 then
![448, 940, 781, 924, 536]
else
![450, 645, 293, 835, 944]))
else
(if i.val < 802 then
(if i.val < 801 then
![451, 490, 298, 538, 945]
else
![452, 932, 944, 945, 538])
else
(if i.val < 803 then
![455, 923, 296, 836, 540]
else
![456, 941, 945, 542, 541]))))
else
(if i.val < 811 then
(if i.val < 807 then
(if i.val < 805 then
![464, 934, 836, 544, 543]
else
(if i.val < 806 then
![465, 758, 702, 895, 946]
else
![467, 363, 946, 628, 546]))
else
(if i.val < 809 then
(if i.val < 808 then
![468, 929, 625, 547, 947]
else
![469, 942, 302, 947, 547])
else
(if i.val < 810 then
![473, 475, 629, 549, 948]
else
![474, 928, 621, 948, 549])))
else
(if i.val < 815 then
(if i.val < 813 then
(if i.val < 812 then
![475, 769, 699, 605, 949]
else
![477, 306, 949, 902, 551])
else
(if i.val < 814 then
![480, 771, 704, 900, 552]
else
![483, 933, 897, 555, 554]))
else
(if i.val < 817 then
(if i.val < 816 then
![484, 775, 305, 849, 950]
else
![485, 629, 413, 556, 951])
else
(if i.val < 818 then
![486, 630, 950, 951, 556]
else
![489, 492, 951, 559, 558])))))
else
(if i.val < 834 then
(if i.val < 826 then
(if i.val < 822 then
(if i.val < 820 then
![490, 699, 309, 612, 952]
else
(if i.val < 821 then
![492, 943, 952, 614, 560]
else
![494, 314, 633, 562, 561]))
else
(if i.val < 824 then
(if i.val < 823 then
![496, 704, 312, 904, 563]
else
![497, 924, 321, 565, 564])
else
(if i.val < 825 then
![501, 944, 314, 856, 567]
else
![502, 951, 325, 569, 568])))
else
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
![505, 613, 904, 855, 570]
else
![509, 465, 632, 858, 953])
else
(if i.val < 829 then
![510, 325, 953, 574, 573]
else
![514, 901, 855, 576, 575]))
else
(if i.val < 832 then
(if i.val < 831 then
![515, 468, 570, 577, 954]
else
![516, 469, 406, 954, 577])
else
(if i.val < 833 then
![518, 324, 947, 863, 579]
else
![519, 863, 850, 581, 580]))))
else
(if i.val < 842 then
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
![730, 327, 473, 742, 955]
else
![726, 370, 543, 799, 956])
else
(if i.val < 837 then
![732, 955, 956, 802, 584]
else
![915, 373, 747, 585, 957]))
else
(if i.val < 840 then
(if i.val < 839 then
![938, 374, 329, 957, 585]
else
![918, 802, 778, 587, 586])
else
(if i.val < 841 then
![914, 379, 741, 943, 588]
else
![939, 332, 489, 757, 590])))
else
(if i.val < 846 then
(if i.val < 844 then
(if i.val < 843 then
![735, 543, 330, 753, 958]
else
![908, 384, 335, 591, 959])
else
(if i.val < 845 then
![940, 385, 958, 959, 591]
else
![910, 757, 774, 593, 592]))
else
(if i.val < 848 then
(if i.val < 847 then
![941, 393, 779, 596, 595]
else
![909, 801, 959, 927, 597])
else
(if i.val < 849 then
![916, 768, 957, 921, 599]
else
![758, 509, 580, 815, 960])))))))
else
(if i.val < 911 then
(if i.val < 880 then
(if i.val < 865 then
(if i.val < 857 then
(if i.val < 853 then
(if i.val < 851 then
![761, 428, 960, 698, 602]
else
(if i.val < 852 then
![929, 515, 695, 603, 961]
else
![942, 516, 341, 961, 603]))
else
(if i.val < 855 then
(if i.val < 854 then
![928, 770, 691, 949, 605]
else
![769, 473, 575, 676, 962])
else
(if i.val < 856 then
![773, 345, 962, 826, 607]
else
![771, 956, 582, 824, 608])))
else
(if i.val < 861 then
(if i.val < 859 then
(if i.val < 858 then
![933, 957, 821, 611, 610]
else
![775, 739, 344, 827, 963])
else
(if i.val < 860 then
![932, 700, 963, 952, 612]
else
![777, 575, 348, 683, 964]))
else
(if i.val < 863 then
(if i.val < 862 then
![943, 489, 964, 685, 615]
else
![926, 353, 703, 617, 616])
else
(if i.val < 864 then
![781, 582, 351, 832, 618]
else
![924, 959, 359, 620, 619]))))
else
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
![944, 756, 353, 893, 622]
else
(if i.val < 867 then
![945, 952, 363, 624, 623]
else
![923, 684, 832, 892, 625]))
else
(if i.val < 870 then
(if i.val < 869 then
![925, 825, 892, 630, 629]
else
![930, 362, 961, 898, 631])
else
(if i.val < 871 then
![934, 898, 828, 633, 632]
else
![702, 383, 364, 722, 965])))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
![895, 815, 729, 635, 966]
else
![946, 960, 965, 966, 635])
else
(if i.val < 875 then
![947, 961, 731, 638, 637]
else
![948, 949, 734, 640, 639]))
else
(if i.val < 878 then
(if i.val < 877 then
![699, 451, 369, 709, 967]
else
![949, 962, 967, 712, 641])
else
(if i.val < 879 then
![902, 376, 736, 643, 642]
else
![704, 965, 372, 791, 644])))))
else
(if i.val < 895 then
(if i.val < 887 then
(if i.val < 883 then
(if i.val < 881 then
![900, 824, 788, 646, 645]
else
(if i.val < 882 then
![897, 788, 403, 939, 648]
else
![950, 963, 376, 906, 650]))
else
(if i.val < 885 then
(if i.val < 884 then
![951, 734, 939, 652, 651]
else
![952, 967, 382, 718, 655])
else
(if i.val < 886 then
![904, 791, 890, 659, 658]
else
![891, 810, 387, 911, 661])))
else
(if i.val < 891 then
(if i.val < 889 then
(if i.val < 888 then
![953, 946, 737, 912, 666]
else
![896, 398, 966, 913, 668])
else
(if i.val < 890 then
![901, 913, 792, 670, 669]
else
![954, 947, 665, 673, 672]))
else
(if i.val < 893 then
(if i.val < 892 then
![770, 474, 566, 962, 676]
else
![955, 410, 948, 867, 678])
else
(if i.val < 894 then
![956, 480, 634, 865, 679]
else
![957, 483, 862, 682, 681]))))
else
(if i.val < 903 then
(if i.val < 899 then
(if i.val < 897 then
(if i.val < 896 then
![739, 484, 409, 805, 968]
else
![778, 576, 968, 964, 683])
else
(if i.val < 898 then
![757, 418, 581, 687, 686]
else
![958, 634, 416, 869, 688]))
else
(if i.val < 901 then
(if i.val < 900 then
![959, 497, 424, 690, 689]
else
![756, 501, 418, 813, 692])
else
(if i.val < 902 then
![779, 964, 428, 694, 693]
else
![754, 557, 869, 812, 695])))
else
(if i.val < 907 then
(if i.val < 905 then
(if i.val < 904 then
![927, 866, 812, 700, 699]
else
![768, 427, 954, 822, 701])
else
(if i.val < 906 then
![921, 822, 806, 703, 702]
else
![960, 953, 675, 882, 705]))
else
(if i.val < 909 then
(if i.val < 908 then
![961, 954, 878, 708, 707]
else
![689, 564, 431, 786, 969])
else
(if i.val < 910 then
![700, 452, 969, 967, 709]
else
![691, 881, 434, 787, 711]))))))
else
(if i.val < 941 then
(if i.val < 926 then
(if i.val < 918 then
(if i.val < 914 then
(if i.val < 912 then
![962, 948, 671, 886, 713]
else
(if i.val < 913 then
![963, 968, 441, 887, 717]
else
![964, 671, 445, 888, 719]))
else
(if i.val < 916 then
(if i.val < 915 then
![685, 559, 458, 721, 720]
else
![681, 554, 444, 783, 970])
else
(if i.val < 917 then
![703, 885, 970, 965, 722]
else
![893, 813, 464, 727, 726])))
else
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
![684, 455, 888, 784, 729]
else
![892, 784, 875, 731, 730])
else
(if i.val < 921 then
![898, 464, 787, 736, 735]
else
![965, 496, 467, 848, 738]))
else
(if i.val < 924 then
(if i.val < 923 then
![966, 882, 839, 740, 739]
else
![731, 839, 518, 955, 742])
else
(if i.val < 925 then
![725, 969, 471, 798, 744]
else
![734, 502, 955, 746, 745]))))
else
(if i.val < 933 then
(if i.val < 929 then
(if i.val < 927 then
![723, 539, 848, 797, 747]
else
(if i.val < 928 then
![967, 945, 477, 847, 750]
else
![712, 886, 845, 752, 751]))
else
(if i.val < 931 then
(if i.val < 930 then
![707, 672, 476, 793, 971]
else
![736, 544, 971, 958, 753])
else
(if i.val < 932 then
![906, 887, 519, 759, 758]
else
![718, 847, 936, 763, 762])))
else
(if i.val < 937 then
(if i.val < 935 then
(if i.val < 934 then
![716, 970, 494, 795, 765]
else
![737, 958, 510, 767, 766])
else
(if i.val < 936 then
![911, 875, 514, 770, 769]
else
![912, 966, 772, 776, 775]))
else
(if i.val < 939 then
(if i.val < 938 then
![913, 514, 797, 778, 777]
else
![682, 555, 522, 970, 783])
else
(if i.val < 940 then
![687, 525, 654, 881, 785]
else
![690, 565, 920, 969, 786])))))
else
(if i.val < 956 then
(if i.val < 948 then
(if i.val < 944 then
(if i.val < 942 then
![697, 572, 889, 790, 789]
else
(if i.val < 943 then
![708, 673, 532, 971, 793]
else
![721, 654, 937, 840, 796]))
else
(if i.val < 946 then
(if i.val < 945 then
![727, 880, 539, 956, 799]
else
![728, 763, 545, 801, 800])
else
(if i.val < 947 then
![740, 931, 905, 968, 805]
else
![743, 971, 867, 808, 807])))
else
(if i.val < 952 then
(if i.val < 950 then
(if i.val < 949 then
![749, 752, 868, 810, 809]
else
![752, 935, 903, 853, 811])
else
(if i.val < 951 then
![759, 936, 557, 960, 815]
else
![760, 868, 687, 817, 816]))
else
(if i.val < 954 then
(if i.val < 953 then
![763, 903, 562, 859, 819]
else
![776, 740, 870, 963, 827])
else
(if i.val < 955 then
![780, 743, 826, 831, 830]
else
![919, 587, 749, 923, 834]))))
else
(if i.val < 964 then
(if i.val < 960 then
(if i.val < 958 then
(if i.val < 957 then
![917, 646, 804, 944, 835]
else
![970, 649, 926, 838, 837])
else
(if i.val < 959 then
![920, 804, 593, 930, 842]
else
![969, 660, 598, 844, 843]))
else
(if i.val < 962 then
(if i.val < 961 then
![931, 776, 833, 950, 849]
else
![971, 780, 902, 852, 851])
else
(if i.val < 963 then
![935, 749, 829, 891, 854]
else
![936, 922, 613, 953, 858])))
else
(if i.val < 968 then
(if i.val < 966 then
(if i.val < 965 then
![937, 829, 617, 896, 860]
else
![905, 659, 636, 916, 871])
else
(if i.val < 967 then
![968, 950, 918, 873, 872]
else
![903, 728, 643, 909, 876]))
else
(if i.val < 970 then
(if i.val < 969 then
![922, 759, 684, 946, 895]
else
![899, 823, 710, 940, 908])
else
(if i.val < 971 then
![894, 814, 723, 938, 915]
else
![907, 890, 754, 942, 929]))))))))))


end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

def g32p_row21_Nodes00 : Fin 972 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 3 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 6 then
(if i.val < 5 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 7 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 11 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 14 then
(if i.val < 13 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]])
else
(if i.val < 15 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 19 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 22 then
(if i.val < 21 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 23 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 27 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]))
else
(if i.val < 30 then
(if i.val < 29 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 31 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 35 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 38 then
(if i.val < 37 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 39 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 43 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]))
else
(if i.val < 46 then
(if i.val < 45 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 47 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 51 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 54 then
(if i.val < 53 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 55 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 59 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]))
else
(if i.val < 62 then
(if i.val < 61 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 63 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 67 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 70 then
(if i.val < 69 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 71 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 75 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]))
else
(if i.val < 78 then
(if i.val < 77 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 79 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 83 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 86 then
(if i.val < 85 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 87 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 91 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 94 then
(if i.val < 93 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 95 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 99 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 102 then
(if i.val < 101 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 103 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 107 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 110 then
(if i.val < 109 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 111 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 115 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 118 then
(if i.val < 117 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 119 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 123 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 126 then
(if i.val < 125 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 127 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row21_Nodes01 : Fin 972 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 131 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 134 then
(if i.val < 133 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 135 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 139 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 142 then
(if i.val < 141 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 143 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 147 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 150 then
(if i.val < 149 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 151 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 155 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 158 then
(if i.val < 157 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 159 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 163 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 166 then
(if i.val < 165 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 167 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 171 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 174 then
(if i.val < 173 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 175 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 179 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 182 then
(if i.val < 181 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 183 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 187 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 190 then
(if i.val < 189 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 191 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 195 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 198 then
(if i.val < 197 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 199 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 203 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 206 then
(if i.val < 205 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 207 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 211 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 214 then
(if i.val < 213 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 215 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 219 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 222 then
(if i.val < 221 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 223 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]])))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 227 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 230 then
(if i.val < 229 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 231 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 235 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 238 then
(if i.val < 237 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 239 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 243 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 246 then
(if i.val < 245 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 247 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 251 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 254 then
(if i.val < 253 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 255 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row21_Nodes02 : Fin 972 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 259 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 262 then
(if i.val < 261 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 263 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 267 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 270 then
(if i.val < 269 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 271 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 275 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 278 then
(if i.val < 277 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 279 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 283 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 286 then
(if i.val < 285 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 287 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 291 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 294 then
(if i.val < 293 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 295 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 299 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 302 then
(if i.val < 301 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 303 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 307 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 310 then
(if i.val < 309 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 311 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 315 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 318 then
(if i.val < 317 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 319 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 323 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 326 then
(if i.val < 325 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 327 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 331 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 334 then
(if i.val < 333 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 335 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]])
else
(if i.val < 339 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 342 then
(if i.val < 341 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 343 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 347 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 350 then
(if i.val < 349 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 351 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 355 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 358 then
(if i.val < 357 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 359 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 363 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 366 then
(if i.val < 365 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 367 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 371 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 374 then
(if i.val < 373 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 375 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 379 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 382 then
(if i.val < 381 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 383 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row21_Nodes03 : Fin 972 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 387 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 390 then
(if i.val < 389 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 391 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 395 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 398 then
(if i.val < 397 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 399 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 403 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 406 then
(if i.val < 405 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 407 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 411 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 414 then
(if i.val < 413 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 415 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 419 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 422 then
(if i.val < 421 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 423 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 427 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 430 then
(if i.val < 429 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 431 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 435 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]))
else
(if i.val < 438 then
(if i.val < 437 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 439 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 443 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 446 then
(if i.val < 445 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]])
else
(if i.val < 447 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 451 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 454 then
(if i.val < 453 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 455 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 459 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 462 then
(if i.val < 461 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 463 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 467 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 470 then
(if i.val < 469 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 471 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 475 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 478 then
(if i.val < 477 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 479 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 483 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 486 then
(if i.val < 485 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 487 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 491 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 494 then
(if i.val < 493 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 495 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 499 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 502 then
(if i.val < 501 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 503 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 507 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 510 then
(if i.val < 509 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 511 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row21_Nodes04 : Fin 972 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 515 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 518 then
(if i.val < 517 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 519 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 523 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 526 then
(if i.val < 525 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 527 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]])
else
(if i.val < 531 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 534 then
(if i.val < 533 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 535 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]])))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 539 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 542 then
(if i.val < 541 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 543 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 547 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 550 then
(if i.val < 549 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 551 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 555 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 558 then
(if i.val < 557 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 559 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 563 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 566 then
(if i.val < 565 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 567 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 571 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 574 then
(if i.val < 573 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 575 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 579 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 582 then
(if i.val < 581 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 583 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 587 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 590 then
(if i.val < 589 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 591 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 595 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 598 then
(if i.val < 597 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 599 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]])
else
(if i.val < 603 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 606 then
(if i.val < 605 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 607 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]])))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 611 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 614 then
(if i.val < 613 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 615 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])
else
(if i.val < 619 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 622 then
(if i.val < 621 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 623 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 627 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 630 then
(if i.val < 629 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 631 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 635 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 638 then
(if i.val < 637 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 639 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row21_Nodes05 : Fin 972 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 643 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 646 then
(if i.val < 645 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 647 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 651 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 654 then
(if i.val < 653 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 655 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 659 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 662 then
(if i.val < 661 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 663 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 667 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 670 then
(if i.val < 669 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 671 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]])
else
(if i.val < 675 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 678 then
(if i.val < 677 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 679 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 683 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 686 then
(if i.val < 685 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 687 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 691 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 694 then
(if i.val < 693 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 695 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])
else
(if i.val < 699 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 702 then
(if i.val < 701 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 703 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 707 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]))
else
(if i.val < 710 then
(if i.val < 709 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 711 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 715 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 718 then
(if i.val < 717 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 719 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 723 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 726 then
(if i.val < 725 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 727 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 731 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 734 then
(if i.val < 733 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 735 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 739 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 742 then
(if i.val < 741 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 743 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]])))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 747 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 750 then
(if i.val < 749 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 751 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 755 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 758 then
(if i.val < 757 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 759 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 763 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 766 then
(if i.val < 765 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]])
else
(if i.val < 767 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row21_Nodes06 : Fin 972 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 771 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 774 then
(if i.val < 773 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])
else
(if i.val < 775 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 779 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 782 then
(if i.val < 781 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 783 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 787 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 790 then
(if i.val < 789 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 791 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 795 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 798 then
(if i.val < 797 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]])
else
(if i.val < 799 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 803 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 806 then
(if i.val < 805 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 807 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 811 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 814 then
(if i.val < 813 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 815 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 819 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 822 then
(if i.val < 821 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 823 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 827 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 830 then
(if i.val < 829 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 831 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 835 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 838 then
(if i.val < 837 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 839 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 843 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 846 then
(if i.val < 845 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 847 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 851 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]))
else
(if i.val < 854 then
(if i.val < 853 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 855 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]])))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])
else
(if i.val < 859 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 862 then
(if i.val < 861 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 863 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 867 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 870 then
(if i.val < 869 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 871 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 875 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 878 then
(if i.val < 877 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 879 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 883 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 886 then
(if i.val < 885 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 887 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 891 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 894 then
(if i.val < 893 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 895 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row21_Nodes07 : Fin 972 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 934 then
(if i.val < 915 then
(if i.val < 905 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 899 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 902 then
(if i.val < 901 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 903 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
(if i.val < 904 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))))
else
(if i.val < 910 then
(if i.val < 907 then
(if i.val < 906 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 908 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]
else
(if i.val < 909 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]])))
else
(if i.val < 912 then
(if i.val < 911 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])
else
(if i.val < 913 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
(if i.val < 914 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])))))
else
(if i.val < 924 then
(if i.val < 919 then
(if i.val < 917 then
(if i.val < 916 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 918 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 921 then
(if i.val < 920 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 922 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
(if i.val < 923 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 929 then
(if i.val < 926 then
(if i.val < 925 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 927 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
(if i.val < 928 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 931 then
(if i.val < 930 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 932 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
(if i.val < 933 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]))))))
else
(if i.val < 953 then
(if i.val < 943 then
(if i.val < 938 then
(if i.val < 936 then
(if i.val < 935 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 937 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 940 then
(if i.val < 939 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 941 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
(if i.val < 942 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 948 then
(if i.val < 945 then
(if i.val < 944 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 946 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
(if i.val < 947 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 950 then
(if i.val < 949 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 951 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
(if i.val < 952 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 962 then
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 956 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 959 then
(if i.val < 958 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 960 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
(if i.val < 961 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]))))
else
(if i.val < 967 then
(if i.val < 964 then
(if i.val < 963 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 965 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
(if i.val < 966 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 969 then
(if i.val < 968 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 970 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
(if i.val < 971 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])))))))


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row21_groupParent : Fin 972 → Fin 972 :=
  fun i => (if i.val < 486 then
(if i.val < 243 then
(if i.val < 121 then
(if i.val < 60 then
(if i.val < 30 then
(if i.val < 15 then
(if i.val < 7 then
(if i.val < 3 then
(if i.val < 1 then
0
else
(if i.val < 2 then
0
else
0))
else
(if i.val < 5 then
(if i.val < 4 then
0
else
0)
else
(if i.val < 6 then
0
else
1)))
else
(if i.val < 11 then
(if i.val < 9 then
(if i.val < 8 then
1
else
1)
else
(if i.val < 10 then
1
else
1))
else
(if i.val < 13 then
(if i.val < 12 then
2
else
2)
else
(if i.val < 14 then
2
else
2))))
else
(if i.val < 22 then
(if i.val < 18 then
(if i.val < 16 then
3
else
(if i.val < 17 then
3
else
3))
else
(if i.val < 20 then
(if i.val < 19 then
3
else
4)
else
(if i.val < 21 then
4
else
6)))
else
(if i.val < 26 then
(if i.val < 24 then
(if i.val < 23 then
6
else
6)
else
(if i.val < 25 then
6
else
7))
else
(if i.val < 28 then
(if i.val < 27 then
7
else
7)
else
(if i.val < 29 then
7
else
8)))))
else
(if i.val < 45 then
(if i.val < 37 then
(if i.val < 33 then
(if i.val < 31 then
8
else
(if i.val < 32 then
8
else
8))
else
(if i.val < 35 then
(if i.val < 34 then
9
else
9)
else
(if i.val < 36 then
11
else
11)))
else
(if i.val < 41 then
(if i.val < 39 then
(if i.val < 38 then
11
else
12)
else
(if i.val < 40 then
12
else
12))
else
(if i.val < 43 then
(if i.val < 42 then
12
else
13)
else
(if i.val < 44 then
13
else
15))))
else
(if i.val < 52 then
(if i.val < 48 then
(if i.val < 46 then
15
else
(if i.val < 47 then
15
else
15))
else
(if i.val < 50 then
(if i.val < 49 then
16
else
16)
else
(if i.val < 51 then
16
else
17)))
else
(if i.val < 56 then
(if i.val < 54 then
(if i.val < 53 then
17
else
19)
else
(if i.val < 55 then
19
else
19))
else
(if i.val < 58 then
(if i.val < 57 then
19
else
21)
else
(if i.val < 59 then
21
else
21))))))
else
(if i.val < 90 then
(if i.val < 75 then
(if i.val < 67 then
(if i.val < 63 then
(if i.val < 61 then
21
else
(if i.val < 62 then
22
else
22))
else
(if i.val < 65 then
(if i.val < 64 then
22
else
22)
else
(if i.val < 66 then
23
else
23)))
else
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
25
else
25)
else
(if i.val < 70 then
25
else
26))
else
(if i.val < 73 then
(if i.val < 72 then
26
else
26)
else
(if i.val < 74 then
26
else
27))))
else
(if i.val < 82 then
(if i.val < 78 then
(if i.val < 76 then
27
else
(if i.val < 77 then
29
else
29))
else
(if i.val < 80 then
(if i.val < 79 then
29
else
29)
else
(if i.val < 81 then
30
else
30)))
else
(if i.val < 86 then
(if i.val < 84 then
(if i.val < 83 then
30
else
31)
else
(if i.val < 85 then
31
else
33))
else
(if i.val < 88 then
(if i.val < 87 then
33
else
33)
else
(if i.val < 89 then
33
else
35)))))
else
(if i.val < 105 then
(if i.val < 97 then
(if i.val < 93 then
(if i.val < 91 then
35
else
(if i.val < 92 then
35
else
35))
else
(if i.val < 95 then
(if i.val < 94 then
36
else
36)
else
(if i.val < 96 then
38
else
38)))
else
(if i.val < 101 then
(if i.val < 99 then
(if i.val < 98 then
38
else
38)
else
(if i.val < 100 then
39
else
39))
else
(if i.val < 103 then
(if i.val < 102 then
39
else
40)
else
(if i.val < 104 then
40
else
42))))
else
(if i.val < 113 then
(if i.val < 109 then
(if i.val < 107 then
(if i.val < 106 then
42
else
42)
else
(if i.val < 108 then
42
else
44))
else
(if i.val < 111 then
(if i.val < 110 then
44
else
44)
else
(if i.val < 112 then
45
else
45)))
else
(if i.val < 117 then
(if i.val < 115 then
(if i.val < 114 then
45
else
45)
else
(if i.val < 116 then
46
else
46))
else
(if i.val < 119 then
(if i.val < 118 then
48
else
48)
else
(if i.val < 120 then
48
else
48)))))))
else
(if i.val < 182 then
(if i.val < 151 then
(if i.val < 136 then
(if i.val < 128 then
(if i.val < 124 then
(if i.val < 122 then
49
else
(if i.val < 123 then
49
else
51))
else
(if i.val < 126 then
(if i.val < 125 then
51
else
51)
else
(if i.val < 127 then
53
else
53)))
else
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
53
else
53)
else
(if i.val < 131 then
54
else
54))
else
(if i.val < 134 then
(if i.val < 133 then
54
else
55)
else
(if i.val < 135 then
57
else
57))))
else
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
57
else
(if i.val < 138 then
58
else
58))
else
(if i.val < 141 then
(if i.val < 140 then
58
else
58)
else
(if i.val < 142 then
59
else
59)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
61
else
61)
else
(if i.val < 146 then
61
else
61))
else
(if i.val < 149 then
(if i.val < 148 then
62
else
62)
else
(if i.val < 150 then
62
else
63)))))
else
(if i.val < 166 then
(if i.val < 158 then
(if i.val < 154 then
(if i.val < 152 then
63
else
(if i.val < 153 then
65
else
65))
else
(if i.val < 156 then
(if i.val < 155 then
65
else
65)
else
(if i.val < 157 then
67
else
67)))
else
(if i.val < 162 then
(if i.val < 160 then
(if i.val < 159 then
67
else
67)
else
(if i.val < 161 then
68
else
68))
else
(if i.val < 164 then
(if i.val < 163 then
70
else
70)
else
(if i.val < 165 then
70
else
70))))
else
(if i.val < 174 then
(if i.val < 170 then
(if i.val < 168 then
(if i.val < 167 then
71
else
71)
else
(if i.val < 169 then
71
else
72))
else
(if i.val < 172 then
(if i.val < 171 then
72
else
74)
else
(if i.val < 173 then
74
else
74)))
else
(if i.val < 178 then
(if i.val < 176 then
(if i.val < 175 then
74
else
76)
else
(if i.val < 177 then
76
else
76))
else
(if i.val < 180 then
(if i.val < 179 then
77
else
77)
else
(if i.val < 181 then
77
else
77))))))
else
(if i.val < 212 then
(if i.val < 197 then
(if i.val < 189 then
(if i.val < 185 then
(if i.val < 183 then
78
else
(if i.val < 184 then
78
else
80))
else
(if i.val < 187 then
(if i.val < 186 then
80
else
80)
else
(if i.val < 188 then
80
else
81)))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
81
else
83)
else
(if i.val < 192 then
83
else
83))
else
(if i.val < 195 then
(if i.val < 194 then
85
else
85)
else
(if i.val < 196 then
85
else
85))))
else
(if i.val < 204 then
(if i.val < 200 then
(if i.val < 198 then
86
else
(if i.val < 199 then
86
else
86))
else
(if i.val < 202 then
(if i.val < 201 then
87
else
89)
else
(if i.val < 203 then
89
else
89)))
else
(if i.val < 208 then
(if i.val < 206 then
(if i.val < 205 then
89
else
90)
else
(if i.val < 207 then
90
else
90))
else
(if i.val < 210 then
(if i.val < 209 then
91
else
91)
else
(if i.val < 211 then
93
else
93)))))
else
(if i.val < 227 then
(if i.val < 219 then
(if i.val < 215 then
(if i.val < 213 then
93
else
(if i.val < 214 then
93
else
95))
else
(if i.val < 217 then
(if i.val < 216 then
95
else
95)
else
(if i.val < 218 then
96
else
96)))
else
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
96
else
96)
else
(if i.val < 222 then
97
else
97))
else
(if i.val < 225 then
(if i.val < 224 then
99
else
99)
else
(if i.val < 226 then
99
else
99))))
else
(if i.val < 235 then
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
100
else
100)
else
(if i.val < 230 then
102
else
102))
else
(if i.val < 233 then
(if i.val < 232 then
102
else
104)
else
(if i.val < 234 then
104
else
104)))
else
(if i.val < 239 then
(if i.val < 237 then
(if i.val < 236 then
105
else
105)
else
(if i.val < 238 then
105
else
106))
else
(if i.val < 241 then
(if i.val < 240 then
108
else
108)
else
(if i.val < 242 then
108
else
108))))))))
else
(if i.val < 364 then
(if i.val < 303 then
(if i.val < 273 then
(if i.val < 258 then
(if i.val < 250 then
(if i.val < 246 then
(if i.val < 244 then
109
else
(if i.val < 245 then
109
else
111))
else
(if i.val < 248 then
(if i.val < 247 then
111
else
111)
else
(if i.val < 249 then
111
else
112)))
else
(if i.val < 254 then
(if i.val < 252 then
(if i.val < 251 then
112
else
113)
else
(if i.val < 253 then
113
else
115))
else
(if i.val < 256 then
(if i.val < 255 then
115
else
115)
else
(if i.val < 257 then
117
else
117))))
else
(if i.val < 265 then
(if i.val < 261 then
(if i.val < 259 then
117
else
(if i.val < 260 then
118
else
118))
else
(if i.val < 263 then
(if i.val < 262 then
118
else
119)
else
(if i.val < 264 then
119
else
121)))
else
(if i.val < 269 then
(if i.val < 267 then
(if i.val < 266 then
121
else
121)
else
(if i.val < 268 then
123
else
123))
else
(if i.val < 271 then
(if i.val < 270 then
123
else
124)
else
(if i.val < 272 then
126
else
126)))))
else
(if i.val < 288 then
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
126
else
(if i.val < 275 then
127
else
127))
else
(if i.val < 278 then
(if i.val < 277 then
127
else
128)
else
(if i.val < 279 then
128
else
130)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
130
else
130)
else
(if i.val < 283 then
131
else
134))
else
(if i.val < 286 then
(if i.val < 285 then
134
else
134)
else
(if i.val < 287 then
134
else
135))))
else
(if i.val < 295 then
(if i.val < 291 then
(if i.val < 289 then
135
else
(if i.val < 290 then
137
else
137))
else
(if i.val < 293 then
(if i.val < 292 then
137
else
138)
else
(if i.val < 294 then
138
else
138)))
else
(if i.val < 299 then
(if i.val < 297 then
(if i.val < 296 then
139
else
139)
else
(if i.val < 298 then
141
else
141))
else
(if i.val < 301 then
(if i.val < 300 then
141
else
143)
else
(if i.val < 302 then
143
else
143))))))
else
(if i.val < 333 then
(if i.val < 318 then
(if i.val < 310 then
(if i.val < 306 then
(if i.val < 304 then
144
else
(if i.val < 305 then
144
else
144))
else
(if i.val < 308 then
(if i.val < 307 then
144
else
145)
else
(if i.val < 309 then
145
else
147)))
else
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
147
else
147)
else
(if i.val < 313 then
147
else
148))
else
(if i.val < 316 then
(if i.val < 315 then
148
else
150)
else
(if i.val < 317 then
150
else
150))))
else
(if i.val < 325 then
(if i.val < 321 then
(if i.val < 319 then
152
else
(if i.val < 320 then
152
else
152))
else
(if i.val < 323 then
(if i.val < 322 then
152
else
153)
else
(if i.val < 324 then
153
else
153)))
else
(if i.val < 329 then
(if i.val < 327 then
(if i.val < 326 then
154
else
156)
else
(if i.val < 328 then
156
else
156))
else
(if i.val < 331 then
(if i.val < 330 then
156
else
157)
else
(if i.val < 332 then
157
else
157)))))
else
(if i.val < 348 then
(if i.val < 340 then
(if i.val < 336 then
(if i.val < 334 then
158
else
(if i.val < 335 then
158
else
160))
else
(if i.val < 338 then
(if i.val < 337 then
160
else
160)
else
(if i.val < 339 then
160
else
162)))
else
(if i.val < 344 then
(if i.val < 342 then
(if i.val < 341 then
162
else
162)
else
(if i.val < 343 then
163
else
163))
else
(if i.val < 346 then
(if i.val < 345 then
163
else
163)
else
(if i.val < 347 then
164
else
164))))
else
(if i.val < 356 then
(if i.val < 352 then
(if i.val < 350 then
(if i.val < 349 then
166
else
166)
else
(if i.val < 351 then
166
else
166))
else
(if i.val < 354 then
(if i.val < 353 then
167
else
167)
else
(if i.val < 355 then
169
else
169)))
else
(if i.val < 360 then
(if i.val < 358 then
(if i.val < 357 then
169
else
171)
else
(if i.val < 359 then
171
else
171))
else
(if i.val < 362 then
(if i.val < 361 then
172
else
172)
else
(if i.val < 363 then
172
else
173)))))))
else
(if i.val < 425 then
(if i.val < 394 then
(if i.val < 379 then
(if i.val < 371 then
(if i.val < 367 then
(if i.val < 365 then
175
else
(if i.val < 366 then
175
else
175))
else
(if i.val < 369 then
(if i.val < 368 then
176
else
176)
else
(if i.val < 370 then
178
else
178)))
else
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
178
else
178)
else
(if i.val < 374 then
179
else
179))
else
(if i.val < 377 then
(if i.val < 376 then
180
else
180)
else
(if i.val < 378 then
182
else
182))))
else
(if i.val < 386 then
(if i.val < 382 then
(if i.val < 380 then
182
else
(if i.val < 381 then
184
else
184))
else
(if i.val < 384 then
(if i.val < 383 then
184
else
185)
else
(if i.val < 385 then
185
else
185)))
else
(if i.val < 390 then
(if i.val < 388 then
(if i.val < 387 then
186
else
186)
else
(if i.val < 389 then
188
else
188))
else
(if i.val < 392 then
(if i.val < 391 then
188
else
190)
else
(if i.val < 393 then
190
else
191)))))
else
(if i.val < 409 then
(if i.val < 401 then
(if i.val < 397 then
(if i.val < 395 then
193
else
(if i.val < 396 then
193
else
194))
else
(if i.val < 399 then
(if i.val < 398 then
194
else
194)
else
(if i.val < 400 then
195
else
195)))
else
(if i.val < 405 then
(if i.val < 403 then
(if i.val < 402 then
197
else
197)
else
(if i.val < 404 then
197
else
198))
else
(if i.val < 407 then
(if i.val < 406 then
201
else
201)
else
(if i.val < 408 then
202
else
202))))
else
(if i.val < 417 then
(if i.val < 413 then
(if i.val < 411 then
(if i.val < 410 then
202
else
202)
else
(if i.val < 412 then
203
else
203))
else
(if i.val < 415 then
(if i.val < 414 then
205
else
205)
else
(if i.val < 416 then
205
else
205)))
else
(if i.val < 421 then
(if i.val < 419 then
(if i.val < 418 then
206
else
206)
else
(if i.val < 420 then
208
else
208))
else
(if i.val < 423 then
(if i.val < 422 then
208
else
210)
else
(if i.val < 424 then
210
else
210))))))
else
(if i.val < 455 then
(if i.val < 440 then
(if i.val < 432 then
(if i.val < 428 then
(if i.val < 426 then
211
else
(if i.val < 427 then
211
else
211))
else
(if i.val < 430 then
(if i.val < 429 then
212
else
214)
else
(if i.val < 431 then
214
else
214)))
else
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
214
else
215)
else
(if i.val < 435 then
215
else
217))
else
(if i.val < 438 then
(if i.val < 437 then
217
else
217)
else
(if i.val < 439 then
218
else
218))))
else
(if i.val < 447 then
(if i.val < 443 then
(if i.val < 441 then
219
else
(if i.val < 442 then
219
else
221))
else
(if i.val < 445 then
(if i.val < 444 then
223
else
223)
else
(if i.val < 446 then
223
else
224)))
else
(if i.val < 451 then
(if i.val < 449 then
(if i.val < 448 then
224
else
224)
else
(if i.val < 450 then
225
else
227))
else
(if i.val < 453 then
(if i.val < 452 then
227
else
227)
else
(if i.val < 454 then
229
else
229)))))
else
(if i.val < 470 then
(if i.val < 462 then
(if i.val < 458 then
(if i.val < 456 then
229
else
(if i.val < 457 then
230
else
232))
else
(if i.val < 460 then
(if i.val < 459 then
232
else
233)
else
(if i.val < 461 then
233
else
235)))
else
(if i.val < 466 then
(if i.val < 464 then
(if i.val < 463 then
235
else
235)
else
(if i.val < 465 then
236
else
239))
else
(if i.val < 468 then
(if i.val < 467 then
239
else
239)
else
(if i.val < 469 then
240
else
240))))
else
(if i.val < 478 then
(if i.val < 474 then
(if i.val < 472 then
(if i.val < 471 then
241
else
241)
else
(if i.val < 473 then
243
else
243))
else
(if i.val < 476 then
(if i.val < 475 then
243
else
245)
else
(if i.val < 477 then
245
else
245)))
else
(if i.val < 482 then
(if i.val < 480 then
(if i.val < 479 then
246
else
246)
else
(if i.val < 481 then
246
else
247))
else
(if i.val < 484 then
(if i.val < 483 then
249
else
249)
else
(if i.val < 485 then
251
else
251)))))))))
else
(if i.val < 729 then
(if i.val < 607 then
(if i.val < 546 then
(if i.val < 516 then
(if i.val < 501 then
(if i.val < 493 then
(if i.val < 489 then
(if i.val < 487 then
251
else
(if i.val < 488 then
253
else
253))
else
(if i.val < 491 then
(if i.val < 490 then
254
else
256)
else
(if i.val < 492 then
256
else
256)))
else
(if i.val < 497 then
(if i.val < 495 then
(if i.val < 494 then
257
else
257)
else
(if i.val < 496 then
259
else
259))
else
(if i.val < 499 then
(if i.val < 498 then
260
else
262)
else
(if i.val < 500 then
262
else
264))))
else
(if i.val < 508 then
(if i.val < 504 then
(if i.val < 502 then
264
else
(if i.val < 503 then
265
else
267))
else
(if i.val < 506 then
(if i.val < 505 then
267
else
267)
else
(if i.val < 507 then
268
else
271)))
else
(if i.val < 512 then
(if i.val < 510 then
(if i.val < 509 then
271
else
272)
else
(if i.val < 511 then
272
else
274))
else
(if i.val < 514 then
(if i.val < 513 then
274
else
274)
else
(if i.val < 515 then
275
else
277)))))
else
(if i.val < 531 then
(if i.val < 523 then
(if i.val < 519 then
(if i.val < 517 then
277
else
(if i.val < 518 then
279
else
279))
else
(if i.val < 521 then
(if i.val < 520 then
280
else
283)
else
(if i.val < 522 then
283
else
283)))
else
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
284
else
284)
else
(if i.val < 526 then
284
else
285))
else
(if i.val < 529 then
(if i.val < 528 then
285
else
287)
else
(if i.val < 530 then
287
else
287))))
else
(if i.val < 538 then
(if i.val < 534 then
(if i.val < 532 then
289
else
(if i.val < 533 then
289
else
290))
else
(if i.val < 536 then
(if i.val < 535 then
290
else
292)
else
(if i.val < 537 then
292
else
292)))
else
(if i.val < 542 then
(if i.val < 540 then
(if i.val < 539 then
293
else
293)
else
(if i.val < 541 then
295
else
295))
else
(if i.val < 544 then
(if i.val < 543 then
295
else
297)
else
(if i.val < 545 then
297
else
298))))))
else
(if i.val < 576 then
(if i.val < 561 then
(if i.val < 553 then
(if i.val < 549 then
(if i.val < 547 then
300
else
(if i.val < 548 then
300
else
300))
else
(if i.val < 551 then
(if i.val < 550 then
301
else
301)
else
(if i.val < 552 then
303
else
303)))
else
(if i.val < 557 then
(if i.val < 555 then
(if i.val < 554 then
303
else
304)
else
(if i.val < 556 then
304
else
305))
else
(if i.val < 559 then
(if i.val < 558 then
305
else
307)
else
(if i.val < 560 then
307
else
309))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
309
else
(if i.val < 563 then
309
else
310))
else
(if i.val < 566 then
(if i.val < 565 then
310
else
310)
else
(if i.val < 567 then
311
else
313)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
313
else
313)
else
(if i.val < 571 then
315
else
315))
else
(if i.val < 574 then
(if i.val < 573 then
316
else
318)
else
(if i.val < 575 then
318
else
319)))))
else
(if i.val < 591 then
(if i.val < 583 then
(if i.val < 579 then
(if i.val < 577 then
319
else
(if i.val < 578 then
320
else
320))
else
(if i.val < 581 then
(if i.val < 580 then
322
else
322)
else
(if i.val < 582 then
322
else
323)))
else
(if i.val < 587 then
(if i.val < 585 then
(if i.val < 584 then
326
else
327)
else
(if i.val < 586 then
327
else
327))
else
(if i.val < 589 then
(if i.val < 588 then
327
else
328)
else
(if i.val < 590 then
328
else
330))))
else
(if i.val < 599 then
(if i.val < 595 then
(if i.val < 593 then
(if i.val < 592 then
330
else
330)
else
(if i.val < 594 then
330
else
331))
else
(if i.val < 597 then
(if i.val < 596 then
333
else
333)
else
(if i.val < 598 then
335
else
335)))
else
(if i.val < 603 then
(if i.val < 601 then
(if i.val < 600 then
336
else
336)
else
(if i.val < 602 then
337
else
339))
else
(if i.val < 605 then
(if i.val < 604 then
339
else
339)
else
(if i.val < 606 then
340
else
340)))))))
else
(if i.val < 668 then
(if i.val < 637 then
(if i.val < 622 then
(if i.val < 614 then
(if i.val < 610 then
(if i.val < 608 then
342
else
(if i.val < 609 then
342
else
342))
else
(if i.val < 612 then
(if i.val < 611 then
343
else
343)
else
(if i.val < 613 then
344
else
344)))
else
(if i.val < 618 then
(if i.val < 616 then
(if i.val < 615 then
346
else
348)
else
(if i.val < 617 then
348
else
348))
else
(if i.val < 620 then
(if i.val < 619 then
349
else
349)
else
(if i.val < 621 then
349
else
350))))
else
(if i.val < 629 then
(if i.val < 625 then
(if i.val < 623 then
352
else
(if i.val < 624 then
352
else
352))
else
(if i.val < 627 then
(if i.val < 626 then
354
else
354)
else
(if i.val < 628 then
355
else
357)))
else
(if i.val < 633 then
(if i.val < 631 then
(if i.val < 630 then
358
else
358)
else
(if i.val < 632 then
360
else
360))
else
(if i.val < 635 then
(if i.val < 634 then
360
else
361)
else
(if i.val < 636 then
364
else
364)))))
else
(if i.val < 652 then
(if i.val < 644 then
(if i.val < 640 then
(if i.val < 638 then
365
else
(if i.val < 639 then
365
else
367))
else
(if i.val < 642 then
(if i.val < 641 then
367
else
369)
else
(if i.val < 643 then
369
else
369)))
else
(if i.val < 648 then
(if i.val < 646 then
(if i.val < 645 then
370
else
370)
else
(if i.val < 647 then
370
else
371))
else
(if i.val < 650 then
(if i.val < 649 then
373
else
373)
else
(if i.val < 651 then
375
else
375))))
else
(if i.val < 660 then
(if i.val < 656 then
(if i.val < 654 then
(if i.val < 653 then
375
else
377)
else
(if i.val < 655 then
378
else
380))
else
(if i.val < 658 then
(if i.val < 657 then
380
else
381)
else
(if i.val < 659 then
383
else
383)))
else
(if i.val < 664 then
(if i.val < 662 then
(if i.val < 661 then
384
else
386)
else
(if i.val < 663 then
386
else
388))
else
(if i.val < 666 then
(if i.val < 665 then
389
else
391)
else
(if i.val < 667 then
394
else
394))))))
else
(if i.val < 698 then
(if i.val < 683 then
(if i.val < 675 then
(if i.val < 671 then
(if i.val < 669 then
396
else
(if i.val < 670 then
396
else
396))
else
(if i.val < 673 then
(if i.val < 672 then
397
else
399)
else
(if i.val < 674 then
399
else
401)))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
402
else
405)
else
(if i.val < 678 then
405
else
407))
else
(if i.val < 681 then
(if i.val < 680 then
407
else
407)
else
(if i.val < 682 then
408
else
408))))
else
(if i.val < 690 then
(if i.val < 686 then
(if i.val < 684 then
409
else
(if i.val < 685 then
409
else
411))
else
(if i.val < 688 then
(if i.val < 687 then
413
else
413)
else
(if i.val < 689 then
414
else
414)))
else
(if i.val < 694 then
(if i.val < 692 then
(if i.val < 691 then
414
else
415)
else
(if i.val < 693 then
417
else
417))
else
(if i.val < 696 then
(if i.val < 695 then
417
else
419)
else
(if i.val < 697 then
419
else
420)))))
else
(if i.val < 713 then
(if i.val < 705 then
(if i.val < 701 then
(if i.val < 699 then
422
else
(if i.val < 700 then
423
else
423))
else
(if i.val < 703 then
(if i.val < 702 then
425
else
425)
else
(if i.val < 704 then
425
else
426)))
else
(if i.val < 709 then
(if i.val < 707 then
(if i.val < 706 then
429
else
429)
else
(if i.val < 708 then
430
else
430))
else
(if i.val < 711 then
(if i.val < 710 then
431
else
431)
else
(if i.val < 712 then
433
else
433))))
else
(if i.val < 721 then
(if i.val < 717 then
(if i.val < 715 then
(if i.val < 714 then
435
else
435)
else
(if i.val < 716 then
436
else
438))
else
(if i.val < 719 then
(if i.val < 718 then
440
else
440)
else
(if i.val < 720 then
443
else
443)))
else
(if i.val < 725 then
(if i.val < 723 then
(if i.val < 722 then
443
else
444)
else
(if i.val < 724 then
444
else
446))
else
(if i.val < 727 then
(if i.val < 726 then
447
else
450)
else
(if i.val < 728 then
450
else
451))))))))
else
(if i.val < 850 then
(if i.val < 789 then
(if i.val < 759 then
(if i.val < 744 then
(if i.val < 736 then
(if i.val < 732 then
(if i.val < 730 then
453
else
(if i.val < 731 then
453
else
453))
else
(if i.val < 734 then
(if i.val < 733 then
454
else
457)
else
(if i.val < 735 then
459
else
461)))
else
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
461
else
462)
else
(if i.val < 739 then
465
else
465))
else
(if i.val < 742 then
(if i.val < 741 then
465
else
466)
else
(if i.val < 743 then
468
else
468))))
else
(if i.val < 751 then
(if i.val < 747 then
(if i.val < 745 then
470
else
(if i.val < 746 then
470
else
470))
else
(if i.val < 749 then
(if i.val < 748 then
472
else
472)
else
(if i.val < 750 then
473
else
475)))
else
(if i.val < 755 then
(if i.val < 753 then
(if i.val < 752 then
475
else
475)
else
(if i.val < 754 then
476
else
476))
else
(if i.val < 757 then
(if i.val < 756 then
478
else
479)
else
(if i.val < 758 then
482
else
484)))))
else
(if i.val < 774 then
(if i.val < 766 then
(if i.val < 762 then
(if i.val < 760 then
484
else
(if i.val < 761 then
485
else
487))
else
(if i.val < 764 then
(if i.val < 763 then
490
else
490)
else
(if i.val < 765 then
491
else
493)))
else
(if i.val < 770 then
(if i.val < 768 then
(if i.val < 767 then
493
else
493)
else
(if i.val < 769 then
495
else
498))
else
(if i.val < 772 then
(if i.val < 771 then
498
else
500)
else
(if i.val < 773 then
503
else
504))))
else
(if i.val < 781 then
(if i.val < 777 then
(if i.val < 775 then
507
else
(if i.val < 776 then
509
else
509))
else
(if i.val < 779 then
(if i.val < 778 then
511
else
511)
else
(if i.val < 780 then
512
else
515)))
else
(if i.val < 785 then
(if i.val < 783 then
(if i.val < 782 then
517
else
520)
else
(if i.val < 784 then
521
else
521))
else
(if i.val < 787 then
(if i.val < 786 then
523
else
523)
else
(if i.val < 788 then
523
else
524))))))
else
(if i.val < 819 then
(if i.val < 804 then
(if i.val < 796 then
(if i.val < 792 then
(if i.val < 790 then
526
else
(if i.val < 791 then
526
else
528))
else
(if i.val < 794 then
(if i.val < 793 then
529
else
531)
else
(if i.val < 795 then
531
else
533)))
else
(if i.val < 800 then
(if i.val < 798 then
(if i.val < 797 then
535
else
535)
else
(if i.val < 799 then
536
else
538))
else
(if i.val < 802 then
(if i.val < 801 then
538
else
538)
else
(if i.val < 803 then
540
else
541))))
else
(if i.val < 811 then
(if i.val < 807 then
(if i.val < 805 then
543
else
(if i.val < 806 then
546
else
546))
else
(if i.val < 809 then
(if i.val < 808 then
547
else
547)
else
(if i.val < 810 then
549
else
549)))
else
(if i.val < 815 then
(if i.val < 813 then
(if i.val < 812 then
551
else
551)
else
(if i.val < 814 then
552
else
554))
else
(if i.val < 817 then
(if i.val < 816 then
556
else
556)
else
(if i.val < 818 then
556
else
558)))))
else
(if i.val < 834 then
(if i.val < 826 then
(if i.val < 822 then
(if i.val < 820 then
560
else
(if i.val < 821 then
560
else
561))
else
(if i.val < 824 then
(if i.val < 823 then
563
else
564)
else
(if i.val < 825 then
567
else
568)))
else
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
570
else
573)
else
(if i.val < 829 then
573
else
575))
else
(if i.val < 832 then
(if i.val < 831 then
577
else
577)
else
(if i.val < 833 then
579
else
580))))
else
(if i.val < 842 then
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
584
else
584)
else
(if i.val < 837 then
584
else
585))
else
(if i.val < 840 then
(if i.val < 839 then
585
else
586)
else
(if i.val < 841 then
588
else
590)))
else
(if i.val < 846 then
(if i.val < 844 then
(if i.val < 843 then
591
else
591)
else
(if i.val < 845 then
591
else
592))
else
(if i.val < 848 then
(if i.val < 847 then
595
else
597)
else
(if i.val < 849 then
599
else
602)))))))
else
(if i.val < 911 then
(if i.val < 880 then
(if i.val < 865 then
(if i.val < 857 then
(if i.val < 853 then
(if i.val < 851 then
602
else
(if i.val < 852 then
603
else
603))
else
(if i.val < 855 then
(if i.val < 854 then
605
else
607)
else
(if i.val < 856 then
607
else
608)))
else
(if i.val < 861 then
(if i.val < 859 then
(if i.val < 858 then
610
else
612)
else
(if i.val < 860 then
612
else
615))
else
(if i.val < 863 then
(if i.val < 862 then
615
else
616)
else
(if i.val < 864 then
618
else
619))))
else
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
622
else
(if i.val < 867 then
623
else
625))
else
(if i.val < 870 then
(if i.val < 869 then
629
else
631)
else
(if i.val < 871 then
632
else
635)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
635
else
635)
else
(if i.val < 875 then
637
else
639))
else
(if i.val < 878 then
(if i.val < 877 then
641
else
641)
else
(if i.val < 879 then
642
else
644)))))
else
(if i.val < 895 then
(if i.val < 887 then
(if i.val < 883 then
(if i.val < 881 then
645
else
(if i.val < 882 then
648
else
650))
else
(if i.val < 885 then
(if i.val < 884 then
651
else
655)
else
(if i.val < 886 then
658
else
661)))
else
(if i.val < 891 then
(if i.val < 889 then
(if i.val < 888 then
666
else
668)
else
(if i.val < 890 then
669
else
672))
else
(if i.val < 893 then
(if i.val < 892 then
676
else
678)
else
(if i.val < 894 then
679
else
681))))
else
(if i.val < 903 then
(if i.val < 899 then
(if i.val < 897 then
(if i.val < 896 then
683
else
683)
else
(if i.val < 898 then
686
else
688))
else
(if i.val < 901 then
(if i.val < 900 then
689
else
692)
else
(if i.val < 902 then
693
else
695)))
else
(if i.val < 907 then
(if i.val < 905 then
(if i.val < 904 then
699
else
701)
else
(if i.val < 906 then
702
else
705))
else
(if i.val < 909 then
(if i.val < 908 then
707
else
709)
else
(if i.val < 910 then
709
else
711))))))
else
(if i.val < 941 then
(if i.val < 926 then
(if i.val < 918 then
(if i.val < 914 then
(if i.val < 912 then
713
else
(if i.val < 913 then
717
else
719))
else
(if i.val < 916 then
(if i.val < 915 then
720
else
722)
else
(if i.val < 917 then
722
else
726)))
else
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
729
else
730)
else
(if i.val < 921 then
735
else
738))
else
(if i.val < 924 then
(if i.val < 923 then
739
else
742)
else
(if i.val < 925 then
744
else
745))))
else
(if i.val < 933 then
(if i.val < 929 then
(if i.val < 927 then
747
else
(if i.val < 928 then
750
else
751))
else
(if i.val < 931 then
(if i.val < 930 then
753
else
753)
else
(if i.val < 932 then
758
else
762)))
else
(if i.val < 937 then
(if i.val < 935 then
(if i.val < 934 then
765
else
766)
else
(if i.val < 936 then
769
else
775))
else
(if i.val < 939 then
(if i.val < 938 then
777
else
783)
else
(if i.val < 940 then
785
else
786)))))
else
(if i.val < 956 then
(if i.val < 948 then
(if i.val < 944 then
(if i.val < 942 then
789
else
(if i.val < 943 then
793
else
796))
else
(if i.val < 946 then
(if i.val < 945 then
799
else
800)
else
(if i.val < 947 then
805
else
807)))
else
(if i.val < 952 then
(if i.val < 950 then
(if i.val < 949 then
809
else
811)
else
(if i.val < 951 then
815
else
816))
else
(if i.val < 954 then
(if i.val < 953 then
819
else
827)
else
(if i.val < 955 then
830
else
834))))
else
(if i.val < 964 then
(if i.val < 960 then
(if i.val < 958 then
(if i.val < 957 then
835
else
837)
else
(if i.val < 959 then
842
else
843))
else
(if i.val < 962 then
(if i.val < 961 then
849
else
851)
else
(if i.val < 963 then
854
else
858)))
else
(if i.val < 968 then
(if i.val < 966 then
(if i.val < 965 then
860
else
871)
else
(if i.val < 967 then
872
else
876))
else
(if i.val < 970 then
(if i.val < 969 then
895
else
908)
else
(if i.val < 971 then
915
else
929))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row21_characterValues : Fin 972 → Multiplicative (ZMod 3) :=
  fun i => (if i.val < 486 then
(if i.val < 243 then
(if i.val < 121 then
(if i.val < 60 then
(if i.val < 30 then
(if i.val < 15 then
(if i.val < 7 then
(if i.val < 3 then
(if i.val < 1 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 2 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 5 then
(if i.val < 4 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 6 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 11 then
(if i.val < 9 then
(if i.val < 8 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 10 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 13 then
(if i.val < 12 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 14 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 22 then
(if i.val < 18 then
(if i.val < 16 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 17 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 20 then
(if i.val < 19 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 21 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 26 then
(if i.val < 24 then
(if i.val < 23 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 25 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 28 then
(if i.val < 27 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 29 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 45 then
(if i.val < 37 then
(if i.val < 33 then
(if i.val < 31 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 32 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 35 then
(if i.val < 34 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 36 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 41 then
(if i.val < 39 then
(if i.val < 38 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 40 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 43 then
(if i.val < 42 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 44 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 52 then
(if i.val < 48 then
(if i.val < 46 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 47 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 50 then
(if i.val < 49 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 51 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 56 then
(if i.val < 54 then
(if i.val < 53 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 55 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 58 then
(if i.val < 57 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 59 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))))
else
(if i.val < 90 then
(if i.val < 75 then
(if i.val < 67 then
(if i.val < 63 then
(if i.val < 61 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 62 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 65 then
(if i.val < 64 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 66 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 70 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 73 then
(if i.val < 72 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 74 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 82 then
(if i.val < 78 then
(if i.val < 76 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 77 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 80 then
(if i.val < 79 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 81 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 86 then
(if i.val < 84 then
(if i.val < 83 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 85 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 88 then
(if i.val < 87 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 89 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))
else
(if i.val < 105 then
(if i.val < 97 then
(if i.val < 93 then
(if i.val < 91 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 92 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 95 then
(if i.val < 94 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 96 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 101 then
(if i.val < 99 then
(if i.val < 98 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 100 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 103 then
(if i.val < 102 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 104 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 113 then
(if i.val < 109 then
(if i.val < 107 then
(if i.val < 106 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 108 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 111 then
(if i.val < 110 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 112 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 117 then
(if i.val < 115 then
(if i.val < 114 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 116 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 119 then
(if i.val < 118 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 120 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))))))
else
(if i.val < 182 then
(if i.val < 151 then
(if i.val < 136 then
(if i.val < 128 then
(if i.val < 124 then
(if i.val < 122 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 123 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 126 then
(if i.val < 125 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 127 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 131 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 134 then
(if i.val < 133 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 135 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 138 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 141 then
(if i.val < 140 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 142 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 146 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 149 then
(if i.val < 148 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 150 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 166 then
(if i.val < 158 then
(if i.val < 154 then
(if i.val < 152 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 153 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 156 then
(if i.val < 155 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 157 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 162 then
(if i.val < 160 then
(if i.val < 159 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 161 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 164 then
(if i.val < 163 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 165 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 174 then
(if i.val < 170 then
(if i.val < 168 then
(if i.val < 167 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 169 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 172 then
(if i.val < 171 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 173 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 178 then
(if i.val < 176 then
(if i.val < 175 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 177 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 180 then
(if i.val < 179 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 181 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))))
else
(if i.val < 212 then
(if i.val < 197 then
(if i.val < 189 then
(if i.val < 185 then
(if i.val < 183 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 184 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 187 then
(if i.val < 186 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 188 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 192 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 195 then
(if i.val < 194 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 196 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 204 then
(if i.val < 200 then
(if i.val < 198 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 199 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 202 then
(if i.val < 201 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 203 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 208 then
(if i.val < 206 then
(if i.val < 205 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 207 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 210 then
(if i.val < 209 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 211 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))))
else
(if i.val < 227 then
(if i.val < 219 then
(if i.val < 215 then
(if i.val < 213 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 214 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 217 then
(if i.val < 216 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 218 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 222 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 225 then
(if i.val < 224 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 226 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 235 then
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 230 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 233 then
(if i.val < 232 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 234 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 239 then
(if i.val < 237 then
(if i.val < 236 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 238 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 241 then
(if i.val < 240 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 242 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))))))
else
(if i.val < 364 then
(if i.val < 303 then
(if i.val < 273 then
(if i.val < 258 then
(if i.val < 250 then
(if i.val < 246 then
(if i.val < 244 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 245 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 248 then
(if i.val < 247 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 249 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 254 then
(if i.val < 252 then
(if i.val < 251 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 253 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 256 then
(if i.val < 255 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 257 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 265 then
(if i.val < 261 then
(if i.val < 259 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 260 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 263 then
(if i.val < 262 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 264 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 269 then
(if i.val < 267 then
(if i.val < 266 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 268 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 271 then
(if i.val < 270 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 272 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))
else
(if i.val < 288 then
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 275 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 278 then
(if i.val < 277 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 279 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 283 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 286 then
(if i.val < 285 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 287 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 295 then
(if i.val < 291 then
(if i.val < 289 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 290 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 293 then
(if i.val < 292 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 294 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 299 then
(if i.val < 297 then
(if i.val < 296 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 298 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 301 then
(if i.val < 300 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 302 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))))
else
(if i.val < 333 then
(if i.val < 318 then
(if i.val < 310 then
(if i.val < 306 then
(if i.val < 304 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 305 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 308 then
(if i.val < 307 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 309 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 313 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 316 then
(if i.val < 315 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 317 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 325 then
(if i.val < 321 then
(if i.val < 319 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 320 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 323 then
(if i.val < 322 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 324 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 329 then
(if i.val < 327 then
(if i.val < 326 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 328 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 331 then
(if i.val < 330 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 332 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))
else
(if i.val < 348 then
(if i.val < 340 then
(if i.val < 336 then
(if i.val < 334 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 335 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 338 then
(if i.val < 337 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 339 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 344 then
(if i.val < 342 then
(if i.val < 341 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 343 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 346 then
(if i.val < 345 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 347 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 356 then
(if i.val < 352 then
(if i.val < 350 then
(if i.val < 349 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 351 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 354 then
(if i.val < 353 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 355 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 360 then
(if i.val < 358 then
(if i.val < 357 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 359 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 362 then
(if i.val < 361 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 363 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))))
else
(if i.val < 425 then
(if i.val < 394 then
(if i.val < 379 then
(if i.val < 371 then
(if i.val < 367 then
(if i.val < 365 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 366 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 369 then
(if i.val < 368 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 370 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 374 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 377 then
(if i.val < 376 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 378 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 386 then
(if i.val < 382 then
(if i.val < 380 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 381 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 384 then
(if i.val < 383 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 385 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 390 then
(if i.val < 388 then
(if i.val < 387 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 389 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 392 then
(if i.val < 391 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 393 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))
else
(if i.val < 409 then
(if i.val < 401 then
(if i.val < 397 then
(if i.val < 395 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 396 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 399 then
(if i.val < 398 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 400 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 405 then
(if i.val < 403 then
(if i.val < 402 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 404 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 407 then
(if i.val < 406 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 408 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 417 then
(if i.val < 413 then
(if i.val < 411 then
(if i.val < 410 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 412 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 415 then
(if i.val < 414 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 416 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 421 then
(if i.val < 419 then
(if i.val < 418 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 420 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 423 then
(if i.val < 422 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 424 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))))
else
(if i.val < 455 then
(if i.val < 440 then
(if i.val < 432 then
(if i.val < 428 then
(if i.val < 426 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 427 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 430 then
(if i.val < 429 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 431 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 435 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 438 then
(if i.val < 437 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 439 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 447 then
(if i.val < 443 then
(if i.val < 441 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 442 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 445 then
(if i.val < 444 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 446 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 451 then
(if i.val < 449 then
(if i.val < 448 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 450 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 453 then
(if i.val < 452 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 454 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 470 then
(if i.val < 462 then
(if i.val < 458 then
(if i.val < 456 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 457 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 460 then
(if i.val < 459 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 461 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 466 then
(if i.val < 464 then
(if i.val < 463 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 465 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 468 then
(if i.val < 467 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 469 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 478 then
(if i.val < 474 then
(if i.val < 472 then
(if i.val < 471 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 473 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 476 then
(if i.val < 475 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 477 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 482 then
(if i.val < 480 then
(if i.val < 479 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 481 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 484 then
(if i.val < 483 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 485 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))))))
else
(if i.val < 729 then
(if i.val < 607 then
(if i.val < 546 then
(if i.val < 516 then
(if i.val < 501 then
(if i.val < 493 then
(if i.val < 489 then
(if i.val < 487 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 488 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 491 then
(if i.val < 490 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 492 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 497 then
(if i.val < 495 then
(if i.val < 494 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 496 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 499 then
(if i.val < 498 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 500 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 508 then
(if i.val < 504 then
(if i.val < 502 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 503 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 506 then
(if i.val < 505 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 507 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 512 then
(if i.val < 510 then
(if i.val < 509 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 511 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 514 then
(if i.val < 513 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 515 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))))
else
(if i.val < 531 then
(if i.val < 523 then
(if i.val < 519 then
(if i.val < 517 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 518 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 521 then
(if i.val < 520 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 522 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 526 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 529 then
(if i.val < 528 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 530 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 538 then
(if i.val < 534 then
(if i.val < 532 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 533 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 536 then
(if i.val < 535 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 537 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 542 then
(if i.val < 540 then
(if i.val < 539 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 541 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 544 then
(if i.val < 543 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 545 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))))
else
(if i.val < 576 then
(if i.val < 561 then
(if i.val < 553 then
(if i.val < 549 then
(if i.val < 547 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 548 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 551 then
(if i.val < 550 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 552 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 557 then
(if i.val < 555 then
(if i.val < 554 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 556 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 559 then
(if i.val < 558 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 560 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 563 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 566 then
(if i.val < 565 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 567 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 571 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 574 then
(if i.val < 573 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 575 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 591 then
(if i.val < 583 then
(if i.val < 579 then
(if i.val < 577 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 578 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 581 then
(if i.val < 580 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 582 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 587 then
(if i.val < 585 then
(if i.val < 584 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 586 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 589 then
(if i.val < 588 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 590 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 599 then
(if i.val < 595 then
(if i.val < 593 then
(if i.val < 592 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 594 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 597 then
(if i.val < 596 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 598 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 603 then
(if i.val < 601 then
(if i.val < 600 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 602 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 605 then
(if i.val < 604 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 606 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))))
else
(if i.val < 668 then
(if i.val < 637 then
(if i.val < 622 then
(if i.val < 614 then
(if i.val < 610 then
(if i.val < 608 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 609 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 612 then
(if i.val < 611 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 613 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 618 then
(if i.val < 616 then
(if i.val < 615 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 617 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 620 then
(if i.val < 619 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 621 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 629 then
(if i.val < 625 then
(if i.val < 623 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 624 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 627 then
(if i.val < 626 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 628 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 633 then
(if i.val < 631 then
(if i.val < 630 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 632 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 635 then
(if i.val < 634 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 636 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))
else
(if i.val < 652 then
(if i.val < 644 then
(if i.val < 640 then
(if i.val < 638 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 639 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 642 then
(if i.val < 641 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 643 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 648 then
(if i.val < 646 then
(if i.val < 645 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 647 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 650 then
(if i.val < 649 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 651 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 660 then
(if i.val < 656 then
(if i.val < 654 then
(if i.val < 653 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 655 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 658 then
(if i.val < 657 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 659 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 664 then
(if i.val < 662 then
(if i.val < 661 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 663 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 666 then
(if i.val < 665 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 667 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))))
else
(if i.val < 698 then
(if i.val < 683 then
(if i.val < 675 then
(if i.val < 671 then
(if i.val < 669 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 670 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 673 then
(if i.val < 672 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 674 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 678 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 681 then
(if i.val < 680 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 682 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 690 then
(if i.val < 686 then
(if i.val < 684 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 685 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 688 then
(if i.val < 687 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 689 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 694 then
(if i.val < 692 then
(if i.val < 691 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 693 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 696 then
(if i.val < 695 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 697 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))))
else
(if i.val < 713 then
(if i.val < 705 then
(if i.val < 701 then
(if i.val < 699 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 700 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 703 then
(if i.val < 702 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 704 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 709 then
(if i.val < 707 then
(if i.val < 706 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 708 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 711 then
(if i.val < 710 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 712 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 721 then
(if i.val < 717 then
(if i.val < 715 then
(if i.val < 714 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 716 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 719 then
(if i.val < 718 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 720 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 725 then
(if i.val < 723 then
(if i.val < 722 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 724 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 727 then
(if i.val < 726 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 728 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))))))
else
(if i.val < 850 then
(if i.val < 789 then
(if i.val < 759 then
(if i.val < 744 then
(if i.val < 736 then
(if i.val < 732 then
(if i.val < 730 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 731 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 734 then
(if i.val < 733 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 735 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 739 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 742 then
(if i.val < 741 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 743 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 751 then
(if i.val < 747 then
(if i.val < 745 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 746 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 749 then
(if i.val < 748 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 750 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 755 then
(if i.val < 753 then
(if i.val < 752 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 754 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 757 then
(if i.val < 756 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 758 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))
else
(if i.val < 774 then
(if i.val < 766 then
(if i.val < 762 then
(if i.val < 760 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 761 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 764 then
(if i.val < 763 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 765 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 770 then
(if i.val < 768 then
(if i.val < 767 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 769 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 772 then
(if i.val < 771 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 773 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 781 then
(if i.val < 777 then
(if i.val < 775 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 776 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 779 then
(if i.val < 778 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 780 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 785 then
(if i.val < 783 then
(if i.val < 782 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 784 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 787 then
(if i.val < 786 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 788 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))))
else
(if i.val < 819 then
(if i.val < 804 then
(if i.val < 796 then
(if i.val < 792 then
(if i.val < 790 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 791 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 794 then
(if i.val < 793 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 795 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 800 then
(if i.val < 798 then
(if i.val < 797 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 799 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 802 then
(if i.val < 801 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 803 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 811 then
(if i.val < 807 then
(if i.val < 805 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 806 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 809 then
(if i.val < 808 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 810 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 815 then
(if i.val < 813 then
(if i.val < 812 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 814 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 817 then
(if i.val < 816 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 818 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 834 then
(if i.val < 826 then
(if i.val < 822 then
(if i.val < 820 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 821 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 824 then
(if i.val < 823 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 825 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 829 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 832 then
(if i.val < 831 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 833 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 842 then
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 837 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 840 then
(if i.val < 839 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 841 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 846 then
(if i.val < 844 then
(if i.val < 843 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 845 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 848 then
(if i.val < 847 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 849 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))))))
else
(if i.val < 911 then
(if i.val < 880 then
(if i.val < 865 then
(if i.val < 857 then
(if i.val < 853 then
(if i.val < 851 then
Multiplicative.ofAdd (1 : ZMod 3)
else
(if i.val < 852 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 855 then
(if i.val < 854 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 856 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))))
else
(if i.val < 861 then
(if i.val < 859 then
(if i.val < 858 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 860 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 863 then
(if i.val < 862 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 864 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))))
else
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 867 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 870 then
(if i.val < 869 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 871 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 875 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 878 then
(if i.val < 877 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 879 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))))
else
(if i.val < 895 then
(if i.val < 887 then
(if i.val < 883 then
(if i.val < 881 then
Multiplicative.ofAdd (2 : ZMod 3)
else
(if i.val < 882 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 885 then
(if i.val < 884 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 886 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 891 then
(if i.val < 889 then
(if i.val < 888 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 890 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 893 then
(if i.val < 892 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 894 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 903 then
(if i.val < 899 then
(if i.val < 897 then
(if i.val < 896 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 898 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 901 then
(if i.val < 900 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 902 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 907 then
(if i.val < 905 then
(if i.val < 904 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 906 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 909 then
(if i.val < 908 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 910 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))))
else
(if i.val < 941 then
(if i.val < 926 then
(if i.val < 918 then
(if i.val < 914 then
(if i.val < 912 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 913 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 916 then
(if i.val < 915 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 917 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 922 then
(if i.val < 920 then
(if i.val < 919 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 921 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 924 then
(if i.val < 923 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 925 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))))
else
(if i.val < 933 then
(if i.val < 929 then
(if i.val < 927 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 928 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 931 then
(if i.val < 930 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 932 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 937 then
(if i.val < 935 then
(if i.val < 934 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 936 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 939 then
(if i.val < 938 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 940 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))))
else
(if i.val < 956 then
(if i.val < 948 then
(if i.val < 944 then
(if i.val < 942 then
Multiplicative.ofAdd (0 : ZMod 3)
else
(if i.val < 943 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 946 then
(if i.val < 945 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 947 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))))
else
(if i.val < 952 then
(if i.val < 950 then
(if i.val < 949 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 951 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))
else
(if i.val < 954 then
(if i.val < 953 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 955 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))
else
(if i.val < 964 then
(if i.val < 960 then
(if i.val < 958 then
(if i.val < 957 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 959 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3)))
else
(if i.val < 962 then
(if i.val < 961 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (2 : ZMod 3))
else
(if i.val < 963 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))))
else
(if i.val < 968 then
(if i.val < 966 then
(if i.val < 965 then
Multiplicative.ofAdd (0 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3))
else
(if i.val < 967 then
Multiplicative.ofAdd (2 : ZMod 3)
else
Multiplicative.ofAdd (0 : ZMod 3)))
else
(if i.val < 970 then
(if i.val < 969 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3))
else
(if i.val < 971 then
Multiplicative.ofAdd (1 : ZMod 3)
else
Multiplicative.ofAdd (1 : ZMod 3)))))))))))


end HodgeLean.Foundations.Program

end
end
