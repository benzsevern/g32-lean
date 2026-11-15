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

def g32p_row03_groupLabel : Fin 4320 → Fin 2 :=
  fun i => (if i.val < 2160 then
(if i.val < 1080 then
(if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
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
1
else
0))
else
(if i.val < 6 then
(if i.val < 5 then
1
else
0)
else
(if i.val < 7 then
1
else
0)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
1
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
1
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
1
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
1
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
1
else
0)
else
(if i.val < 27 then
1
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
1
else
0)
else
(if i.val < 31 then
1
else
(if i.val < 32 then
0
else
1))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
0
else
1)
else
(if i.val < 36 then
0
else
1))
else
(if i.val < 39 then
(if i.val < 38 then
0
else
1)
else
(if i.val < 40 then
0
else
1)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
0
else
1)
else
(if i.val < 44 then
0
else
1))
else
(if i.val < 47 then
(if i.val < 46 then
0
else
1)
else
(if i.val < 48 then
1
else
(if i.val < 49 then
0
else
1)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
0
else
1)
else
(if i.val < 53 then
0
else
1))
else
(if i.val < 56 then
(if i.val < 55 then
0
else
1)
else
(if i.val < 57 then
0
else
1)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
0
else
1)
else
(if i.val < 61 then
1
else
0))
else
(if i.val < 64 then
(if i.val < 63 then
1
else
0)
else
(if i.val < 65 then
1
else
(if i.val < 66 then
0
else
1)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
0
else
1)
else
(if i.val < 70 then
0
else
1))
else
(if i.val < 73 then
(if i.val < 72 then
0
else
1)
else
(if i.val < 74 then
0
else
1)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
0
else
1)
else
(if i.val < 78 then
1
else
0))
else
(if i.val < 81 then
(if i.val < 80 then
1
else
0)
else
(if i.val < 82 then
1
else
(if i.val < 83 then
0
else
1)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
0
else
1)
else
(if i.val < 87 then
0
else
1))
else
(if i.val < 90 then
(if i.val < 89 then
0
else
1)
else
(if i.val < 91 then
1
else
0)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
1
else
0)
else
(if i.val < 95 then
1
else
0))
else
(if i.val < 98 then
(if i.val < 97 then
1
else
0)
else
(if i.val < 99 then
1
else
(if i.val < 100 then
0
else
1))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
0
else
1)
else
(if i.val < 104 then
0
else
1))
else
(if i.val < 107 then
(if i.val < 106 then
1
else
0)
else
(if i.val < 108 then
1
else
0)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
1
else
0)
else
(if i.val < 112 then
1
else
0))
else
(if i.val < 115 then
(if i.val < 114 then
1
else
0)
else
(if i.val < 116 then
1
else
(if i.val < 117 then
1
else
0)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
1
else
0)
else
(if i.val < 121 then
1
else
0))
else
(if i.val < 124 then
(if i.val < 123 then
1
else
0)
else
(if i.val < 125 then
1
else
0)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
1
else
0)
else
(if i.val < 129 then
1
else
0))
else
(if i.val < 132 then
(if i.val < 131 then
1
else
0)
else
(if i.val < 133 then
1
else
(if i.val < 134 then
1
else
0))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
1
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
0)
else
(if i.val < 142 then
1
else
0)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
1
else
0)
else
(if i.val < 146 then
1
else
1))
else
(if i.val < 149 then
(if i.val < 148 then
0
else
1)
else
(if i.val < 150 then
0
else
1))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
0
else
1)
else
(if i.val < 154 then
0
else
1))
else
(if i.val < 157 then
(if i.val < 156 then
1
else
0)
else
(if i.val < 158 then
1
else
0)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
1
else
1)
else
(if i.val < 162 then
0
else
1))
else
(if i.val < 165 then
(if i.val < 164 then
0
else
1)
else
(if i.val < 166 then
0
else
(if i.val < 167 then
1
else
0))))))
else
(if i.val < 185 then
(if i.val < 176 then
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
1))
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
1)))
else
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
1
else
0)
else
(if i.val < 183 then
1
else
(if i.val < 184 then
1
else
0)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
1
else
0)
else
(if i.val < 188 then
1
else
0))
else
(if i.val < 191 then
(if i.val < 190 then
1
else
0)
else
(if i.val < 192 then
1
else
0)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
1
else
0)
else
(if i.val < 196 then
1
else
1))
else
(if i.val < 199 then
(if i.val < 198 then
0
else
1)
else
(if i.val < 200 then
0
else
(if i.val < 201 then
1
else
0)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
1
else
0)
else
(if i.val < 205 then
1
else
0))
else
(if i.val < 208 then
(if i.val < 207 then
1
else
0)
else
(if i.val < 209 then
1
else
0)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
1
else
1)
else
(if i.val < 213 then
0
else
1))
else
(if i.val < 216 then
(if i.val < 215 then
0
else
1)
else
(if i.val < 217 then
0
else
(if i.val < 218 then
1
else
1)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
1
else
0)
else
(if i.val < 222 then
1
else
0))
else
(if i.val < 225 then
(if i.val < 224 then
1
else
0)
else
(if i.val < 226 then
1
else
0)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
1
else
0)
else
(if i.val < 230 then
1
else
0))
else
(if i.val < 233 then
(if i.val < 232 then
1
else
0)
else
(if i.val < 234 then
1
else
(if i.val < 235 then
1
else
0))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
1
else
0)
else
(if i.val < 239 then
1
else
0))
else
(if i.val < 242 then
(if i.val < 241 then
1
else
0)
else
(if i.val < 243 then
1
else
0)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
1
else
0)
else
(if i.val < 247 then
1
else
1))
else
(if i.val < 250 then
(if i.val < 249 then
0
else
1)
else
(if i.val < 251 then
0
else
(if i.val < 252 then
1
else
0)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
1
else
0)
else
(if i.val < 256 then
1
else
1))
else
(if i.val < 259 then
(if i.val < 258 then
0
else
1)
else
(if i.val < 260 then
0
else
1)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
1
else
0)
else
(if i.val < 264 then
1
else
0))
else
(if i.val < 267 then
(if i.val < 266 then
1
else
0)
else
(if i.val < 268 then
1
else
(if i.val < 269 then
0
else
1)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
0
else
1)
else
(if i.val < 273 then
1
else
0))
else
(if i.val < 276 then
(if i.val < 275 then
1
else
0)
else
(if i.val < 277 then
1
else
0)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
0
else
1)
else
(if i.val < 281 then
0
else
1))
else
(if i.val < 284 then
(if i.val < 283 then
0
else
1)
else
(if i.val < 285 then
1
else
0))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
1
else
0)
else
(if i.val < 289 then
1
else
0))
else
(if i.val < 292 then
(if i.val < 291 then
1
else
0)
else
(if i.val < 293 then
1
else
0)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
1
else
1)
else
(if i.val < 297 then
0
else
1))
else
(if i.val < 300 then
(if i.val < 299 then
0
else
1)
else
(if i.val < 301 then
0
else
(if i.val < 302 then
1
else
0))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
1
else
0)
else
(if i.val < 306 then
1
else
0))
else
(if i.val < 309 then
(if i.val < 308 then
1
else
0)
else
(if i.val < 310 then
1
else
1)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
0
else
1)
else
(if i.val < 314 then
0
else
1))
else
(if i.val < 317 then
(if i.val < 316 then
0
else
1)
else
(if i.val < 318 then
1
else
(if i.val < 319 then
0
else
1)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
0
else
1)
else
(if i.val < 323 then
0
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
1
else
0)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
1
else
0)
else
(if i.val < 331 then
1
else
0))
else
(if i.val < 334 then
(if i.val < 333 then
1
else
0)
else
(if i.val < 335 then
1
else
(if i.val < 336 then
0
else
1)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
1
else
0)
else
(if i.val < 340 then
1
else
0))
else
(if i.val < 343 then
(if i.val < 342 then
1
else
0)
else
(if i.val < 344 then
1
else
0)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
1
else
1)
else
(if i.val < 348 then
0
else
1))
else
(if i.val < 351 then
(if i.val < 350 then
0
else
1)
else
(if i.val < 352 then
1
else
(if i.val < 353 then
0
else
1)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
0
else
1)
else
(if i.val < 357 then
0
else
1))
else
(if i.val < 360 then
(if i.val < 359 then
0
else
1)
else
(if i.val < 361 then
0
else
1)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
1
else
0)
else
(if i.val < 365 then
1
else
0))
else
(if i.val < 368 then
(if i.val < 367 then
1
else
0)
else
(if i.val < 369 then
0
else
(if i.val < 370 then
1
else
0))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
1
else
0)
else
(if i.val < 374 then
1
else
1))
else
(if i.val < 377 then
(if i.val < 376 then
0
else
1)
else
(if i.val < 378 then
0
else
1)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
0
else
1)
else
(if i.val < 382 then
0
else
1))
else
(if i.val < 385 then
(if i.val < 384 then
0
else
1)
else
(if i.val < 386 then
0
else
(if i.val < 387 then
1
else
1)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
0
else
1)
else
(if i.val < 391 then
0
else
1))
else
(if i.val < 394 then
(if i.val < 393 then
0
else
1)
else
(if i.val < 395 then
0
else
1)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
0
else
1)
else
(if i.val < 399 then
0
else
1))
else
(if i.val < 402 then
(if i.val < 401 then
0
else
1)
else
(if i.val < 403 then
1
else
(if i.val < 404 then
0
else
1))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
0
else
1)
else
(if i.val < 408 then
0
else
1))
else
(if i.val < 411 then
(if i.val < 410 then
0
else
1)
else
(if i.val < 412 then
0
else
1)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
0
else
1)
else
(if i.val < 416 then
0
else
1))
else
(if i.val < 419 then
(if i.val < 418 then
1
else
0)
else
(if i.val < 420 then
1
else
0))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
1
else
0)
else
(if i.val < 424 then
1
else
0))
else
(if i.val < 427 then
(if i.val < 426 then
1
else
0)
else
(if i.val < 428 then
1
else
0)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
1
else
1)
else
(if i.val < 432 then
0
else
1))
else
(if i.val < 435 then
(if i.val < 434 then
0
else
1)
else
(if i.val < 436 then
0
else
(if i.val < 437 then
1
else
0))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
1
else
1)
else
(if i.val < 441 then
0
else
1))
else
(if i.val < 444 then
(if i.val < 443 then
0
else
1)
else
(if i.val < 445 then
1
else
0)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
1
else
0)
else
(if i.val < 449 then
1
else
0))
else
(if i.val < 452 then
(if i.val < 451 then
1
else
1)
else
(if i.val < 453 then
0
else
(if i.val < 454 then
1
else
1)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
0
else
1)
else
(if i.val < 458 then
1
else
0))
else
(if i.val < 461 then
(if i.val < 460 then
0
else
1)
else
(if i.val < 462 then
0
else
1)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
0
else
1)
else
(if i.val < 466 then
1
else
0))
else
(if i.val < 469 then
(if i.val < 468 then
1
else
0)
else
(if i.val < 470 then
1
else
(if i.val < 471 then
0
else
1)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
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
1))
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
0)))
else
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
0))
else
(if i.val < 486 then
(if i.val < 485 then
1
else
0)
else
(if i.val < 487 then
1
else
(if i.val < 488 then
0
else
1)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
0
else
1)
else
(if i.val < 492 then
1
else
0))
else
(if i.val < 495 then
(if i.val < 494 then
1
else
0)
else
(if i.val < 496 then
1
else
0)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
1
else
1)
else
(if i.val < 500 then
0
else
1))
else
(if i.val < 503 then
(if i.val < 502 then
0
else
1)
else
(if i.val < 504 then
0
else
(if i.val < 505 then
1
else
0))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
1
else
1)
else
(if i.val < 509 then
0
else
1))
else
(if i.val < 512 then
(if i.val < 511 then
0
else
1)
else
(if i.val < 513 then
0
else
1)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
0
else
1)
else
(if i.val < 517 then
0
else
1))
else
(if i.val < 520 then
(if i.val < 519 then
1
else
0)
else
(if i.val < 521 then
1
else
(if i.val < 522 then
0
else
1)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
0
else
1)
else
(if i.val < 526 then
0
else
1))
else
(if i.val < 529 then
(if i.val < 528 then
0
else
1)
else
(if i.val < 530 then
1
else
0)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
1
else
0)
else
(if i.val < 534 then
1
else
0))
else
(if i.val < 537 then
(if i.val < 536 then
1
else
0)
else
(if i.val < 538 then
1
else
(if i.val < 539 then
1
else
1))))))))))
else
(if i.val < 810 then
(if i.val < 675 then
(if i.val < 607 then
(if i.val < 573 then
(if i.val < 556 then
(if i.val < 548 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
0
else
1)
else
(if i.val < 543 then
0
else
1))
else
(if i.val < 546 then
(if i.val < 545 then
0
else
0)
else
(if i.val < 547 then
1
else
0)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
1
else
0)
else
(if i.val < 551 then
1
else
1))
else
(if i.val < 554 then
(if i.val < 553 then
0
else
1)
else
(if i.val < 555 then
0
else
1))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
0
else
1)
else
(if i.val < 559 then
0
else
1))
else
(if i.val < 562 then
(if i.val < 561 then
0
else
1)
else
(if i.val < 563 then
0
else
1)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
1
else
0)
else
(if i.val < 567 then
1
else
0))
else
(if i.val < 570 then
(if i.val < 569 then
1
else
0)
else
(if i.val < 571 then
1
else
(if i.val < 572 then
0
else
1))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
0
else
1)
else
(if i.val < 576 then
0
else
1))
else
(if i.val < 579 then
(if i.val < 578 then
0
else
1)
else
(if i.val < 580 then
1
else
1)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
0
else
1)
else
(if i.val < 584 then
0
else
1))
else
(if i.val < 587 then
(if i.val < 586 then
1
else
0)
else
(if i.val < 588 then
1
else
(if i.val < 589 then
0
else
1)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
0
else
1)
else
(if i.val < 593 then
1
else
0))
else
(if i.val < 596 then
(if i.val < 595 then
1
else
0)
else
(if i.val < 597 then
1
else
1)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
0
else
0)
else
(if i.val < 601 then
1
else
1))
else
(if i.val < 604 then
(if i.val < 603 then
0
else
1)
else
(if i.val < 605 then
0
else
(if i.val < 606 then
1
else
0)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
1
else
0)
else
(if i.val < 610 then
1
else
0))
else
(if i.val < 613 then
(if i.val < 612 then
1
else
1)
else
(if i.val < 614 then
0
else
1)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
0
else
1)
else
(if i.val < 618 then
0
else
0))
else
(if i.val < 621 then
(if i.val < 620 then
1
else
0)
else
(if i.val < 622 then
1
else
(if i.val < 623 then
0
else
1)))))
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
1
else
0))
else
(if i.val < 630 then
(if i.val < 629 then
1
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
1)
else
(if i.val < 635 then
0
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
0
else
(if i.val < 640 then
1
else
0))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
1
else
0)
else
(if i.val < 644 then
1
else
0))
else
(if i.val < 647 then
(if i.val < 646 then
1
else
1)
else
(if i.val < 648 then
1
else
0)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
1
else
0)
else
(if i.val < 652 then
0
else
1))
else
(if i.val < 655 then
(if i.val < 654 then
1
else
0)
else
(if i.val < 656 then
1
else
(if i.val < 657 then
0
else
1)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
0
else
1)
else
(if i.val < 661 then
0
else
1))
else
(if i.val < 664 then
(if i.val < 663 then
1
else
0)
else
(if i.val < 665 then
1
else
0)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
1
else
0)
else
(if i.val < 669 then
1
else
0))
else
(if i.val < 672 then
(if i.val < 671 then
1
else
0)
else
(if i.val < 673 then
1
else
(if i.val < 674 then
1
else
0))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
1
else
0)
else
(if i.val < 678 then
1
else
0))
else
(if i.val < 681 then
(if i.val < 680 then
1
else
0)
else
(if i.val < 682 then
1
else
1)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
0
else
1)
else
(if i.val < 686 then
0
else
1))
else
(if i.val < 689 then
(if i.val < 688 then
1
else
0)
else
(if i.val < 690 then
1
else
0))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
1
else
0)
else
(if i.val < 694 then
1
else
0))
else
(if i.val < 697 then
(if i.val < 696 then
0
else
1)
else
(if i.val < 698 then
0
else
1)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
0
else
1)
else
(if i.val < 702 then
0
else
0))
else
(if i.val < 705 then
(if i.val < 704 then
1
else
0)
else
(if i.val < 706 then
1
else
(if i.val < 707 then
0
else
1))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
1
else
1)
else
(if i.val < 711 then
0
else
1))
else
(if i.val < 714 then
(if i.val < 713 then
0
else
1)
else
(if i.val < 715 then
0
else
1)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
0
else
1)
else
(if i.val < 719 then
0
else
1))
else
(if i.val < 722 then
(if i.val < 721 then
1
else
1)
else
(if i.val < 723 then
0
else
(if i.val < 724 then
1
else
0)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
0
else
1)
else
(if i.val < 728 then
0
else
1))
else
(if i.val < 731 then
(if i.val < 730 then
0
else
1)
else
(if i.val < 732 then
0
else
1)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
1
else
0)
else
(if i.val < 736 then
1
else
0))
else
(if i.val < 739 then
(if i.val < 738 then
1
else
0)
else
(if i.val < 740 then
1
else
(if i.val < 741 then
0
else
1)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
0
else
1)
else
(if i.val < 745 then
1
else
0))
else
(if i.val < 748 then
(if i.val < 747 then
1
else
0)
else
(if i.val < 749 then
1
else
0)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
1
else
0)
else
(if i.val < 753 then
1
else
1))
else
(if i.val < 756 then
(if i.val < 755 then
0
else
1)
else
(if i.val < 757 then
0
else
(if i.val < 758 then
1
else
1)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
0
else
1)
else
(if i.val < 762 then
0
else
1))
else
(if i.val < 765 then
(if i.val < 764 then
0
else
1)
else
(if i.val < 766 then
1
else
0)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
1
else
1)
else
(if i.val < 770 then
1
else
1))
else
(if i.val < 773 then
(if i.val < 772 then
0
else
0)
else
(if i.val < 774 then
1
else
(if i.val < 775 then
0
else
0))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1
else
1)
else
(if i.val < 779 then
0
else
1))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
1)
else
(if i.val < 783 then
0
else
0)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1
else
0)
else
(if i.val < 787 then
1
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
0
else
(if i.val < 792 then
1
else
0)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
1
else
1)
else
(if i.val < 796 then
0
else
1))
else
(if i.val < 799 then
(if i.val < 798 then
0
else
1)
else
(if i.val < 800 then
0
else
1)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
0
else
1)
else
(if i.val < 804 then
0
else
1))
else
(if i.val < 807 then
(if i.val < 806 then
1
else
1)
else
(if i.val < 808 then
0
else
(if i.val < 809 then
1
else
0)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
1
else
0)
else
(if i.val < 813 then
1
else
1))
else
(if i.val < 816 then
(if i.val < 815 then
0
else
1)
else
(if i.val < 817 then
0
else
1)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
0
else
1)
else
(if i.val < 821 then
0
else
1))
else
(if i.val < 824 then
(if i.val < 823 then
0
else
1)
else
(if i.val < 825 then
1
else
0))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
1
else
0)
else
(if i.val < 829 then
0
else
1))
else
(if i.val < 832 then
(if i.val < 831 then
0
else
1)
else
(if i.val < 833 then
0
else
1)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
1
else
0)
else
(if i.val < 837 then
1
else
0))
else
(if i.val < 840 then
(if i.val < 839 then
1
else
0)
else
(if i.val < 841 then
1
else
(if i.val < 842 then
0
else
1))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
1
else
1)
else
(if i.val < 846 then
0
else
1))
else
(if i.val < 849 then
(if i.val < 848 then
0
else
1)
else
(if i.val < 850 then
0
else
0)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
1
else
0)
else
(if i.val < 854 then
1
else
0))
else
(if i.val < 857 then
(if i.val < 856 then
1
else
1)
else
(if i.val < 858 then
1
else
(if i.val < 859 then
0
else
1)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
0
else
1)
else
(if i.val < 863 then
0
else
1))
else
(if i.val < 866 then
(if i.val < 865 then
0
else
1)
else
(if i.val < 867 then
0
else
1)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
1
else
0)
else
(if i.val < 871 then
1
else
0))
else
(if i.val < 874 then
(if i.val < 873 then
1
else
0)
else
(if i.val < 875 then
1
else
(if i.val < 876 then
0
else
1)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
0
else
1)
else
(if i.val < 880 then
0
else
1))
else
(if i.val < 883 then
(if i.val < 882 then
0
else
1)
else
(if i.val < 884 then
1
else
1)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
0
else
1)
else
(if i.val < 888 then
0
else
1))
else
(if i.val < 891 then
(if i.val < 890 then
1
else
0)
else
(if i.val < 892 then
1
else
(if i.val < 893 then
0
else
1)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
0
else
1)
else
(if i.val < 897 then
1
else
0))
else
(if i.val < 900 then
(if i.val < 899 then
1
else
0)
else
(if i.val < 901 then
1
else
1)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
0
else
0)
else
(if i.val < 905 then
1
else
1))
else
(if i.val < 908 then
(if i.val < 907 then
0
else
1)
else
(if i.val < 909 then
0
else
(if i.val < 910 then
1
else
0))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
1
else
0)
else
(if i.val < 914 then
1
else
0))
else
(if i.val < 917 then
(if i.val < 916 then
1
else
1)
else
(if i.val < 918 then
0
else
1)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
0
else
1)
else
(if i.val < 922 then
0
else
0))
else
(if i.val < 925 then
(if i.val < 924 then
1
else
0)
else
(if i.val < 926 then
1
else
(if i.val < 927 then
0
else
1)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
0
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
0)
else
(if i.val < 935 then
1
else
0)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1
else
0)
else
(if i.val < 939 then
0
else
1))
else
(if i.val < 942 then
(if i.val < 941 then
0
else
1)
else
(if i.val < 943 then
0
else
(if i.val < 944 then
1
else
1))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
1
else
0)
else
(if i.val < 948 then
1
else
0))
else
(if i.val < 951 then
(if i.val < 950 then
1
else
1)
else
(if i.val < 952 then
0
else
1)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
0
else
1)
else
(if i.val < 956 then
0
else
1))
else
(if i.val < 959 then
(if i.val < 958 then
0
else
1)
else
(if i.val < 960 then
1
else
0))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
1
else
0)
else
(if i.val < 964 then
1
else
0))
else
(if i.val < 967 then
(if i.val < 966 then
1
else
0)
else
(if i.val < 968 then
1
else
0)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
1
else
1)
else
(if i.val < 972 then
0
else
1))
else
(if i.val < 975 then
(if i.val < 974 then
0
else
1)
else
(if i.val < 976 then
0
else
(if i.val < 977 then
1
else
0))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
1
else
1)
else
(if i.val < 981 then
0
else
1))
else
(if i.val < 984 then
(if i.val < 983 then
0
else
1)
else
(if i.val < 985 then
1
else
0)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
1
else
0)
else
(if i.val < 989 then
1
else
0))
else
(if i.val < 992 then
(if i.val < 991 then
1
else
0)
else
(if i.val < 993 then
1
else
(if i.val < 994 then
0
else
1)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
0
else
1)
else
(if i.val < 998 then
0
else
0))
else
(if i.val < 1001 then
(if i.val < 1000 then
1
else
0)
else
(if i.val < 1002 then
1
else
0)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
1
else
1)
else
(if i.val < 1006 then
1
else
0))
else
(if i.val < 1009 then
(if i.val < 1008 then
1
else
0)
else
(if i.val < 1010 then
1
else
(if i.val < 1011 then
0
else
1)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
0
else
1)
else
(if i.val < 1015 then
0
else
1))
else
(if i.val < 1018 then
(if i.val < 1017 then
1
else
1)
else
(if i.val < 1019 then
0
else
1)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
0
else
1)
else
(if i.val < 1023 then
0
else
1))
else
(if i.val < 1026 then
(if i.val < 1025 then
0
else
1)
else
(if i.val < 1027 then
1
else
(if i.val < 1028 then
0
else
1)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
1
else
0)
else
(if i.val < 1032 then
1
else
0))
else
(if i.val < 1035 then
(if i.val < 1034 then
1
else
0)
else
(if i.val < 1036 then
1
else
1)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
0
else
1)
else
(if i.val < 1040 then
0
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
0
else
(if i.val < 1045 then
0
else
1))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
0
else
1)
else
(if i.val < 1049 then
0
else
1))
else
(if i.val < 1052 then
(if i.val < 1051 then
1
else
0)
else
(if i.val < 1053 then
1
else
0)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
1
else
0)
else
(if i.val < 1057 then
1
else
1))
else
(if i.val < 1060 then
(if i.val < 1059 then
0
else
1)
else
(if i.val < 1061 then
0
else
(if i.val < 1062 then
1
else
0)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
1
else
1)
else
(if i.val < 1066 then
0
else
1))
else
(if i.val < 1069 then
(if i.val < 1068 then
0
else
1)
else
(if i.val < 1070 then
0
else
1)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
1
else
0)
else
(if i.val < 1074 then
1
else
0))
else
(if i.val < 1077 then
(if i.val < 1076 then
1
else
0)
else
(if i.val < 1078 then
1
else
(if i.val < 1079 then
0
else
1)))))))))))
else
(if i.val < 1620 then
(if i.val < 1350 then
(if i.val < 1215 then
(if i.val < 1147 then
(if i.val < 1113 then
(if i.val < 1096 then
(if i.val < 1088 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
1
else
1)
else
(if i.val < 1083 then
0
else
1))
else
(if i.val < 1086 then
(if i.val < 1085 then
0
else
1)
else
(if i.val < 1087 then
0
else
1)))
else
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
1
else
0)
else
(if i.val < 1095 then
1
else
0))))
else
(if i.val < 1104 then
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
1
else
0)
else
(if i.val < 1099 then
1
else
0))
else
(if i.val < 1102 then
(if i.val < 1101 then
1
else
1)
else
(if i.val < 1103 then
0
else
1)))
else
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
0
else
1)
else
(if i.val < 1107 then
1
else
1))
else
(if i.val < 1110 then
(if i.val < 1109 then
0
else
1)
else
(if i.val < 1111 then
0
else
(if i.val < 1112 then
1
else
0))))))
else
(if i.val < 1130 then
(if i.val < 1121 then
(if i.val < 1117 then
(if i.val < 1115 then
(if i.val < 1114 then
1
else
0)
else
(if i.val < 1116 then
1
else
1))
else
(if i.val < 1119 then
(if i.val < 1118 then
1
else
0)
else
(if i.val < 1120 then
1
else
0)))
else
(if i.val < 1125 then
(if i.val < 1123 then
(if i.val < 1122 then
1
else
0)
else
(if i.val < 1124 then
1
else
0))
else
(if i.val < 1127 then
(if i.val < 1126 then
1
else
0)
else
(if i.val < 1128 then
1
else
(if i.val < 1129 then
0
else
1)))))
else
(if i.val < 1138 then
(if i.val < 1134 then
(if i.val < 1132 then
(if i.val < 1131 then
0
else
1)
else
(if i.val < 1133 then
0
else
1))
else
(if i.val < 1136 then
(if i.val < 1135 then
0
else
1)
else
(if i.val < 1137 then
0
else
1)))
else
(if i.val < 1142 then
(if i.val < 1140 then
(if i.val < 1139 then
0
else
1)
else
(if i.val < 1141 then
1
else
1))
else
(if i.val < 1144 then
(if i.val < 1143 then
0
else
1)
else
(if i.val < 1145 then
0
else
(if i.val < 1146 then
1
else
1)))))))
else
(if i.val < 1181 then
(if i.val < 1164 then
(if i.val < 1155 then
(if i.val < 1151 then
(if i.val < 1149 then
(if i.val < 1148 then
0
else
1)
else
(if i.val < 1150 then
0
else
1))
else
(if i.val < 1153 then
(if i.val < 1152 then
0
else
1)
else
(if i.val < 1154 then
1
else
0)))
else
(if i.val < 1159 then
(if i.val < 1157 then
(if i.val < 1156 then
1
else
0)
else
(if i.val < 1158 then
0
else
0))
else
(if i.val < 1161 then
(if i.val < 1160 then
1
else
1)
else
(if i.val < 1162 then
0
else
(if i.val < 1163 then
0
else
1)))))
else
(if i.val < 1172 then
(if i.val < 1168 then
(if i.val < 1166 then
(if i.val < 1165 then
0
else
1)
else
(if i.val < 1167 then
0
else
1))
else
(if i.val < 1170 then
(if i.val < 1169 then
0
else
1)
else
(if i.val < 1171 then
0
else
1)))
else
(if i.val < 1176 then
(if i.val < 1174 then
(if i.val < 1173 then
0
else
0)
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
0)
else
(if i.val < 1179 then
1
else
(if i.val < 1180 then
1
else
0))))))
else
(if i.val < 1198 then
(if i.val < 1189 then
(if i.val < 1185 then
(if i.val < 1183 then
(if i.val < 1182 then
1
else
0)
else
(if i.val < 1184 then
1
else
0))
else
(if i.val < 1187 then
(if i.val < 1186 then
1
else
0)
else
(if i.val < 1188 then
1
else
1)))
else
(if i.val < 1193 then
(if i.val < 1191 then
(if i.val < 1190 then
0
else
1)
else
(if i.val < 1192 then
0
else
1))
else
(if i.val < 1195 then
(if i.val < 1194 then
0
else
1)
else
(if i.val < 1196 then
0
else
(if i.val < 1197 then
1
else
0)))))
else
(if i.val < 1206 then
(if i.val < 1202 then
(if i.val < 1200 then
(if i.val < 1199 then
1
else
0)
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
0)
else
(if i.val < 1205 then
1
else
0)))
else
(if i.val < 1210 then
(if i.val < 1208 then
(if i.val < 1207 then
1
else
0)
else
(if i.val < 1209 then
1
else
0))
else
(if i.val < 1212 then
(if i.val < 1211 then
0
else
1)
else
(if i.val < 1213 then
1
else
(if i.val < 1214 then
0
else
1))))))))
else
(if i.val < 1282 then
(if i.val < 1248 then
(if i.val < 1231 then
(if i.val < 1223 then
(if i.val < 1219 then
(if i.val < 1217 then
(if i.val < 1216 then
0
else
1)
else
(if i.val < 1218 then
0
else
1))
else
(if i.val < 1221 then
(if i.val < 1220 then
0
else
1)
else
(if i.val < 1222 then
1
else
1)))
else
(if i.val < 1227 then
(if i.val < 1225 then
(if i.val < 1224 then
0
else
1)
else
(if i.val < 1226 then
0
else
1))
else
(if i.val < 1229 then
(if i.val < 1228 then
0
else
1)
else
(if i.val < 1230 then
1
else
1))))
else
(if i.val < 1239 then
(if i.val < 1235 then
(if i.val < 1233 then
(if i.val < 1232 then
0
else
1)
else
(if i.val < 1234 then
1
else
0))
else
(if i.val < 1237 then
(if i.val < 1236 then
1
else
0)
else
(if i.val < 1238 then
1
else
0)))
else
(if i.val < 1243 then
(if i.val < 1241 then
(if i.val < 1240 then
0
else
0)
else
(if i.val < 1242 then
1
else
0))
else
(if i.val < 1245 then
(if i.val < 1244 then
1
else
0)
else
(if i.val < 1246 then
1
else
(if i.val < 1247 then
0
else
1))))))
else
(if i.val < 1265 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
0
else
1)
else
(if i.val < 1251 then
0
else
1))
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
1)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
0
else
1)
else
(if i.val < 1259 then
1
else
0))
else
(if i.val < 1262 then
(if i.val < 1261 then
1
else
0)
else
(if i.val < 1263 then
1
else
(if i.val < 1264 then
0
else
1)))))
else
(if i.val < 1273 then
(if i.val < 1269 then
(if i.val < 1267 then
(if i.val < 1266 then
0
else
1)
else
(if i.val < 1268 then
0
else
1))
else
(if i.val < 1271 then
(if i.val < 1270 then
1
else
0)
else
(if i.val < 1272 then
1
else
0)))
else
(if i.val < 1277 then
(if i.val < 1275 then
(if i.val < 1274 then
1
else
0)
else
(if i.val < 1276 then
1
else
0))
else
(if i.val < 1279 then
(if i.val < 1278 then
1
else
1)
else
(if i.val < 1280 then
1
else
(if i.val < 1281 then
0
else
0)))))))
else
(if i.val < 1316 then
(if i.val < 1299 then
(if i.val < 1290 then
(if i.val < 1286 then
(if i.val < 1284 then
(if i.val < 1283 then
1
else
0)
else
(if i.val < 1285 then
0
else
1))
else
(if i.val < 1288 then
(if i.val < 1287 then
1
else
0)
else
(if i.val < 1289 then
1
else
1)))
else
(if i.val < 1294 then
(if i.val < 1292 then
(if i.val < 1291 then
0
else
0)
else
(if i.val < 1293 then
1
else
0))
else
(if i.val < 1296 then
(if i.val < 1295 then
1
else
1)
else
(if i.val < 1297 then
0
else
(if i.val < 1298 then
1
else
0)))))
else
(if i.val < 1307 then
(if i.val < 1303 then
(if i.val < 1301 then
(if i.val < 1300 then
1
else
0)
else
(if i.val < 1302 then
1
else
1))
else
(if i.val < 1305 then
(if i.val < 1304 then
1
else
0)
else
(if i.val < 1306 then
1
else
0)))
else
(if i.val < 1311 then
(if i.val < 1309 then
(if i.val < 1308 then
1
else
0)
else
(if i.val < 1310 then
1
else
0))
else
(if i.val < 1313 then
(if i.val < 1312 then
1
else
1)
else
(if i.val < 1314 then
1
else
(if i.val < 1315 then
0
else
1))))))
else
(if i.val < 1333 then
(if i.val < 1324 then
(if i.val < 1320 then
(if i.val < 1318 then
(if i.val < 1317 then
0
else
1)
else
(if i.val < 1319 then
1
else
0))
else
(if i.val < 1322 then
(if i.val < 1321 then
1
else
0)
else
(if i.val < 1323 then
1
else
1)))
else
(if i.val < 1328 then
(if i.val < 1326 then
(if i.val < 1325 then
0
else
1)
else
(if i.val < 1327 then
1
else
0))
else
(if i.val < 1330 then
(if i.val < 1329 then
1
else
0)
else
(if i.val < 1331 then
0
else
(if i.val < 1332 then
1
else
0)))))
else
(if i.val < 1341 then
(if i.val < 1337 then
(if i.val < 1335 then
(if i.val < 1334 then
1
else
0)
else
(if i.val < 1336 then
1
else
1))
else
(if i.val < 1339 then
(if i.val < 1338 then
0
else
1)
else
(if i.val < 1340 then
0
else
1)))
else
(if i.val < 1345 then
(if i.val < 1343 then
(if i.val < 1342 then
0
else
1)
else
(if i.val < 1344 then
1
else
1))
else
(if i.val < 1347 then
(if i.val < 1346 then
0
else
1)
else
(if i.val < 1348 then
0
else
(if i.val < 1349 then
1
else
0)))))))))
else
(if i.val < 1485 then
(if i.val < 1417 then
(if i.val < 1383 then
(if i.val < 1366 then
(if i.val < 1358 then
(if i.val < 1354 then
(if i.val < 1352 then
(if i.val < 1351 then
1
else
0)
else
(if i.val < 1353 then
1
else
0))
else
(if i.val < 1356 then
(if i.val < 1355 then
1
else
1)
else
(if i.val < 1357 then
0
else
1)))
else
(if i.val < 1362 then
(if i.val < 1360 then
(if i.val < 1359 then
0
else
1)
else
(if i.val < 1361 then
0
else
1))
else
(if i.val < 1364 then
(if i.val < 1363 then
0
else
1)
else
(if i.val < 1365 then
0
else
1))))
else
(if i.val < 1374 then
(if i.val < 1370 then
(if i.val < 1368 then
(if i.val < 1367 then
0
else
1)
else
(if i.val < 1369 then
0
else
1))
else
(if i.val < 1372 then
(if i.val < 1371 then
0
else
1)
else
(if i.val < 1373 then
0
else
0)))
else
(if i.val < 1378 then
(if i.val < 1376 then
(if i.val < 1375 then
1
else
1)
else
(if i.val < 1377 then
1
else
0))
else
(if i.val < 1380 then
(if i.val < 1379 then
1
else
0)
else
(if i.val < 1381 then
1
else
(if i.val < 1382 then
1
else
0))))))
else
(if i.val < 1400 then
(if i.val < 1391 then
(if i.val < 1387 then
(if i.val < 1385 then
(if i.val < 1384 then
1
else
1)
else
(if i.val < 1386 then
1
else
0))
else
(if i.val < 1389 then
(if i.val < 1388 then
1
else
1)
else
(if i.val < 1390 then
0
else
0)))
else
(if i.val < 1395 then
(if i.val < 1393 then
(if i.val < 1392 then
1
else
1)
else
(if i.val < 1394 then
0
else
1))
else
(if i.val < 1397 then
(if i.val < 1396 then
0
else
1)
else
(if i.val < 1398 then
0
else
(if i.val < 1399 then
1
else
0)))))
else
(if i.val < 1408 then
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
1
else
0)
else
(if i.val < 1403 then
1
else
1))
else
(if i.val < 1406 then
(if i.val < 1405 then
0
else
1)
else
(if i.val < 1407 then
0
else
1)))
else
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
0
else
0)
else
(if i.val < 1411 then
1
else
0))
else
(if i.val < 1414 then
(if i.val < 1413 then
1
else
0)
else
(if i.val < 1415 then
1
else
(if i.val < 1416 then
0
else
1)))))))
else
(if i.val < 1451 then
(if i.val < 1434 then
(if i.val < 1425 then
(if i.val < 1421 then
(if i.val < 1419 then
(if i.val < 1418 then
1
else
1)
else
(if i.val < 1420 then
0
else
0))
else
(if i.val < 1423 then
(if i.val < 1422 then
0
else
1)
else
(if i.val < 1424 then
0
else
1)))
else
(if i.val < 1429 then
(if i.val < 1427 then
(if i.val < 1426 then
0
else
1)
else
(if i.val < 1428 then
1
else
1))
else
(if i.val < 1431 then
(if i.val < 1430 then
0
else
1)
else
(if i.val < 1432 then
0
else
(if i.val < 1433 then
1
else
1)))))
else
(if i.val < 1442 then
(if i.val < 1438 then
(if i.val < 1436 then
(if i.val < 1435 then
0
else
1)
else
(if i.val < 1437 then
0
else
0))
else
(if i.val < 1440 then
(if i.val < 1439 then
1
else
1)
else
(if i.val < 1441 then
1
else
0)))
else
(if i.val < 1446 then
(if i.val < 1444 then
(if i.val < 1443 then
1
else
1)
else
(if i.val < 1445 then
0
else
1))
else
(if i.val < 1448 then
(if i.val < 1447 then
0
else
1)
else
(if i.val < 1449 then
0
else
(if i.val < 1450 then
1
else
1))))))
else
(if i.val < 1468 then
(if i.val < 1459 then
(if i.val < 1455 then
(if i.val < 1453 then
(if i.val < 1452 then
0
else
0)
else
(if i.val < 1454 then
1
else
0))
else
(if i.val < 1457 then
(if i.val < 1456 then
1
else
1)
else
(if i.val < 1458 then
0
else
1)))
else
(if i.val < 1463 then
(if i.val < 1461 then
(if i.val < 1460 then
0
else
1)
else
(if i.val < 1462 then
1
else
0))
else
(if i.val < 1465 then
(if i.val < 1464 then
1
else
0)
else
(if i.val < 1466 then
1
else
(if i.val < 1467 then
0
else
1)))))
else
(if i.val < 1476 then
(if i.val < 1472 then
(if i.val < 1470 then
(if i.val < 1469 then
0
else
1)
else
(if i.val < 1471 then
0
else
1))
else
(if i.val < 1474 then
(if i.val < 1473 then
0
else
1)
else
(if i.val < 1475 then
0
else
0)))
else
(if i.val < 1480 then
(if i.val < 1478 then
(if i.val < 1477 then
1
else
0)
else
(if i.val < 1479 then
1
else
0))
else
(if i.val < 1482 then
(if i.val < 1481 then
1
else
1)
else
(if i.val < 1483 then
1
else
(if i.val < 1484 then
0
else
1))))))))
else
(if i.val < 1552 then
(if i.val < 1518 then
(if i.val < 1501 then
(if i.val < 1493 then
(if i.val < 1489 then
(if i.val < 1487 then
(if i.val < 1486 then
1
else
0)
else
(if i.val < 1488 then
1
else
0))
else
(if i.val < 1491 then
(if i.val < 1490 then
1
else
0)
else
(if i.val < 1492 then
1
else
1)))
else
(if i.val < 1497 then
(if i.val < 1495 then
(if i.val < 1494 then
1
else
0)
else
(if i.val < 1496 then
1
else
0))
else
(if i.val < 1499 then
(if i.val < 1498 then
1
else
0)
else
(if i.val < 1500 then
1
else
0))))
else
(if i.val < 1509 then
(if i.val < 1505 then
(if i.val < 1503 then
(if i.val < 1502 then
1
else
1)
else
(if i.val < 1504 then
0
else
1))
else
(if i.val < 1507 then
(if i.val < 1506 then
1
else
1)
else
(if i.val < 1508 then
1
else
0)))
else
(if i.val < 1513 then
(if i.val < 1511 then
(if i.val < 1510 then
1
else
1)
else
(if i.val < 1512 then
0
else
1))
else
(if i.val < 1515 then
(if i.val < 1514 then
0
else
1)
else
(if i.val < 1516 then
1
else
(if i.val < 1517 then
1
else
0))))))
else
(if i.val < 1535 then
(if i.val < 1526 then
(if i.val < 1522 then
(if i.val < 1520 then
(if i.val < 1519 then
0
else
0)
else
(if i.val < 1521 then
1
else
0))
else
(if i.val < 1524 then
(if i.val < 1523 then
1
else
1)
else
(if i.val < 1525 then
0
else
1)))
else
(if i.val < 1530 then
(if i.val < 1528 then
(if i.val < 1527 then
0
else
1)
else
(if i.val < 1529 then
0
else
1))
else
(if i.val < 1532 then
(if i.val < 1531 then
1
else
0)
else
(if i.val < 1533 then
1
else
(if i.val < 1534 then
0
else
1)))))
else
(if i.val < 1543 then
(if i.val < 1539 then
(if i.val < 1537 then
(if i.val < 1536 then
0
else
1)
else
(if i.val < 1538 then
1
else
0))
else
(if i.val < 1541 then
(if i.val < 1540 then
1
else
0)
else
(if i.val < 1542 then
1
else
0)))
else
(if i.val < 1547 then
(if i.val < 1545 then
(if i.val < 1544 then
1
else
1)
else
(if i.val < 1546 then
0
else
1))
else
(if i.val < 1549 then
(if i.val < 1548 then
1
else
0)
else
(if i.val < 1550 then
1
else
(if i.val < 1551 then
0
else
1)))))))
else
(if i.val < 1586 then
(if i.val < 1569 then
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
1
else
1)
else
(if i.val < 1555 then
0
else
1))
else
(if i.val < 1558 then
(if i.val < 1557 then
0
else
1)
else
(if i.val < 1559 then
0
else
1)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
0
else
1)
else
(if i.val < 1563 then
1
else
1))
else
(if i.val < 1566 then
(if i.val < 1565 then
0
else
1)
else
(if i.val < 1567 then
0
else
(if i.val < 1568 then
1
else
1)))))
else
(if i.val < 1577 then
(if i.val < 1573 then
(if i.val < 1571 then
(if i.val < 1570 then
1
else
0)
else
(if i.val < 1572 then
1
else
0))
else
(if i.val < 1575 then
(if i.val < 1574 then
1
else
0)
else
(if i.val < 1576 then
1
else
0)))
else
(if i.val < 1581 then
(if i.val < 1579 then
(if i.val < 1578 then
1
else
1)
else
(if i.val < 1580 then
1
else
0))
else
(if i.val < 1583 then
(if i.val < 1582 then
1
else
1)
else
(if i.val < 1584 then
1
else
(if i.val < 1585 then
0
else
1))))))
else
(if i.val < 1603 then
(if i.val < 1594 then
(if i.val < 1590 then
(if i.val < 1588 then
(if i.val < 1587 then
0
else
1)
else
(if i.val < 1589 then
0
else
1))
else
(if i.val < 1592 then
(if i.val < 1591 then
0
else
1)
else
(if i.val < 1593 then
0
else
1)))
else
(if i.val < 1598 then
(if i.val < 1596 then
(if i.val < 1595 then
0
else
1)
else
(if i.val < 1597 then
1
else
1))
else
(if i.val < 1600 then
(if i.val < 1599 then
0
else
1)
else
(if i.val < 1601 then
0
else
(if i.val < 1602 then
1
else
1)))))
else
(if i.val < 1611 then
(if i.val < 1607 then
(if i.val < 1605 then
(if i.val < 1604 then
0
else
1)
else
(if i.val < 1606 then
0
else
1))
else
(if i.val < 1609 then
(if i.val < 1608 then
0
else
1)
else
(if i.val < 1610 then
0
else
1)))
else
(if i.val < 1615 then
(if i.val < 1613 then
(if i.val < 1612 then
0
else
0)
else
(if i.val < 1614 then
0
else
1))
else
(if i.val < 1617 then
(if i.val < 1616 then
1
else
0)
else
(if i.val < 1618 then
0
else
(if i.val < 1619 then
1
else
0))))))))))
else
(if i.val < 1890 then
(if i.val < 1755 then
(if i.val < 1687 then
(if i.val < 1653 then
(if i.val < 1636 then
(if i.val < 1628 then
(if i.val < 1624 then
(if i.val < 1622 then
(if i.val < 1621 then
1
else
0)
else
(if i.val < 1623 then
1
else
0))
else
(if i.val < 1626 then
(if i.val < 1625 then
0
else
0)
else
(if i.val < 1627 then
0
else
1)))
else
(if i.val < 1632 then
(if i.val < 1630 then
(if i.val < 1629 then
1
else
0)
else
(if i.val < 1631 then
1
else
1))
else
(if i.val < 1634 then
(if i.val < 1633 then
0
else
0)
else
(if i.val < 1635 then
1
else
0))))
else
(if i.val < 1644 then
(if i.val < 1640 then
(if i.val < 1638 then
(if i.val < 1637 then
1
else
0)
else
(if i.val < 1639 then
1
else
1))
else
(if i.val < 1642 then
(if i.val < 1641 then
0
else
1)
else
(if i.val < 1643 then
0
else
1)))
else
(if i.val < 1648 then
(if i.val < 1646 then
(if i.val < 1645 then
0
else
1)
else
(if i.val < 1647 then
0
else
1))
else
(if i.val < 1650 then
(if i.val < 1649 then
0
else
1)
else
(if i.val < 1651 then
0
else
(if i.val < 1652 then
1
else
1))))))
else
(if i.val < 1670 then
(if i.val < 1661 then
(if i.val < 1657 then
(if i.val < 1655 then
(if i.val < 1654 then
0
else
0)
else
(if i.val < 1656 then
1
else
0))
else
(if i.val < 1659 then
(if i.val < 1658 then
0
else
1)
else
(if i.val < 1660 then
1
else
0)))
else
(if i.val < 1665 then
(if i.val < 1663 then
(if i.val < 1662 then
1
else
0)
else
(if i.val < 1664 then
0
else
1))
else
(if i.val < 1667 then
(if i.val < 1666 then
1
else
1)
else
(if i.val < 1668 then
0
else
(if i.val < 1669 then
1
else
0)))))
else
(if i.val < 1678 then
(if i.val < 1674 then
(if i.val < 1672 then
(if i.val < 1671 then
1
else
0)
else
(if i.val < 1673 then
1
else
1))
else
(if i.val < 1676 then
(if i.val < 1675 then
1
else
0)
else
(if i.val < 1677 then
1
else
1)))
else
(if i.val < 1682 then
(if i.val < 1680 then
(if i.val < 1679 then
0
else
1)
else
(if i.val < 1681 then
0
else
0))
else
(if i.val < 1684 then
(if i.val < 1683 then
0
else
1)
else
(if i.val < 1685 then
1
else
(if i.val < 1686 then
0
else
1)))))))
else
(if i.val < 1721 then
(if i.val < 1704 then
(if i.val < 1695 then
(if i.val < 1691 then
(if i.val < 1689 then
(if i.val < 1688 then
0
else
0)
else
(if i.val < 1690 then
1
else
1))
else
(if i.val < 1693 then
(if i.val < 1692 then
0
else
1)
else
(if i.val < 1694 then
0
else
1)))
else
(if i.val < 1699 then
(if i.val < 1697 then
(if i.val < 1696 then
0
else
1)
else
(if i.val < 1698 then
1
else
0))
else
(if i.val < 1701 then
(if i.val < 1700 then
1
else
0)
else
(if i.val < 1702 then
1
else
(if i.val < 1703 then
0
else
1)))))
else
(if i.val < 1712 then
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
1
else
0)
else
(if i.val < 1707 then
1
else
0))
else
(if i.val < 1710 then
(if i.val < 1709 then
1
else
0)
else
(if i.val < 1711 then
1
else
0)))
else
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
0
else
1)
else
(if i.val < 1715 then
1
else
0))
else
(if i.val < 1718 then
(if i.val < 1717 then
1
else
0)
else
(if i.val < 1719 then
1
else
(if i.val < 1720 then
0
else
1))))))
else
(if i.val < 1738 then
(if i.val < 1729 then
(if i.val < 1725 then
(if i.val < 1723 then
(if i.val < 1722 then
0
else
0)
else
(if i.val < 1724 then
1
else
1))
else
(if i.val < 1727 then
(if i.val < 1726 then
1
else
0)
else
(if i.val < 1728 then
1
else
1)))
else
(if i.val < 1733 then
(if i.val < 1731 then
(if i.val < 1730 then
1
else
1)
else
(if i.val < 1732 then
0
else
1))
else
(if i.val < 1735 then
(if i.val < 1734 then
0
else
1)
else
(if i.val < 1736 then
0
else
(if i.val < 1737 then
0
else
1)))))
else
(if i.val < 1746 then
(if i.val < 1742 then
(if i.val < 1740 then
(if i.val < 1739 then
1
else
0)
else
(if i.val < 1741 then
1
else
1))
else
(if i.val < 1744 then
(if i.val < 1743 then
0
else
1)
else
(if i.val < 1745 then
0
else
1)))
else
(if i.val < 1750 then
(if i.val < 1748 then
(if i.val < 1747 then
0
else
1)
else
(if i.val < 1749 then
0
else
1))
else
(if i.val < 1752 then
(if i.val < 1751 then
0
else
1)
else
(if i.val < 1753 then
1
else
(if i.val < 1754 then
0
else
1))))))))
else
(if i.val < 1822 then
(if i.val < 1788 then
(if i.val < 1771 then
(if i.val < 1763 then
(if i.val < 1759 then
(if i.val < 1757 then
(if i.val < 1756 then
1
else
0)
else
(if i.val < 1758 then
1
else
0))
else
(if i.val < 1761 then
(if i.val < 1760 then
1
else
0)
else
(if i.val < 1762 then
0
else
0)))
else
(if i.val < 1767 then
(if i.val < 1765 then
(if i.val < 1764 then
1
else
1)
else
(if i.val < 1766 then
1
else
0))
else
(if i.val < 1769 then
(if i.val < 1768 then
1
else
0)
else
(if i.val < 1770 then
1
else
1))))
else
(if i.val < 1779 then
(if i.val < 1775 then
(if i.val < 1773 then
(if i.val < 1772 then
0
else
1)
else
(if i.val < 1774 then
0
else
1))
else
(if i.val < 1777 then
(if i.val < 1776 then
0
else
1)
else
(if i.val < 1778 then
1
else
0)))
else
(if i.val < 1783 then
(if i.val < 1781 then
(if i.val < 1780 then
1
else
0)
else
(if i.val < 1782 then
0
else
1))
else
(if i.val < 1785 then
(if i.val < 1784 then
1
else
0)
else
(if i.val < 1786 then
1
else
(if i.val < 1787 then
1
else
0))))))
else
(if i.val < 1805 then
(if i.val < 1796 then
(if i.val < 1792 then
(if i.val < 1790 then
(if i.val < 1789 then
1
else
0)
else
(if i.val < 1791 then
1
else
0))
else
(if i.val < 1794 then
(if i.val < 1793 then
1
else
1)
else
(if i.val < 1795 then
0
else
1)))
else
(if i.val < 1800 then
(if i.val < 1798 then
(if i.val < 1797 then
0
else
1)
else
(if i.val < 1799 then
0
else
1))
else
(if i.val < 1802 then
(if i.val < 1801 then
0
else
1)
else
(if i.val < 1803 then
0
else
(if i.val < 1804 then
1
else
1)))))
else
(if i.val < 1813 then
(if i.val < 1809 then
(if i.val < 1807 then
(if i.val < 1806 then
0
else
1)
else
(if i.val < 1808 then
1
else
0))
else
(if i.val < 1811 then
(if i.val < 1810 then
1
else
0)
else
(if i.val < 1812 then
1
else
1)))
else
(if i.val < 1817 then
(if i.val < 1815 then
(if i.val < 1814 then
0
else
1)
else
(if i.val < 1816 then
0
else
1))
else
(if i.val < 1819 then
(if i.val < 1818 then
1
else
0)
else
(if i.val < 1820 then
1
else
(if i.val < 1821 then
0
else
1)))))))
else
(if i.val < 1856 then
(if i.val < 1839 then
(if i.val < 1830 then
(if i.val < 1826 then
(if i.val < 1824 then
(if i.val < 1823 then
0
else
1)
else
(if i.val < 1825 then
0
else
1))
else
(if i.val < 1828 then
(if i.val < 1827 then
0
else
1)
else
(if i.val < 1829 then
1
else
0)))
else
(if i.val < 1834 then
(if i.val < 1832 then
(if i.val < 1831 then
1
else
0)
else
(if i.val < 1833 then
1
else
1))
else
(if i.val < 1836 then
(if i.val < 1835 then
1
else
1)
else
(if i.val < 1837 then
0
else
(if i.val < 1838 then
1
else
1)))))
else
(if i.val < 1847 then
(if i.val < 1843 then
(if i.val < 1841 then
(if i.val < 1840 then
1
else
0)
else
(if i.val < 1842 then
1
else
0))
else
(if i.val < 1845 then
(if i.val < 1844 then
1
else
1)
else
(if i.val < 1846 then
1
else
1)))
else
(if i.val < 1851 then
(if i.val < 1849 then
(if i.val < 1848 then
1
else
0)
else
(if i.val < 1850 then
1
else
0))
else
(if i.val < 1853 then
(if i.val < 1852 then
1
else
0)
else
(if i.val < 1854 then
1
else
(if i.val < 1855 then
0
else
1))))))
else
(if i.val < 1873 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
0
else
1)
else
(if i.val < 1859 then
1
else
1))
else
(if i.val < 1862 then
(if i.val < 1861 then
0
else
1)
else
(if i.val < 1863 then
0
else
1)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
1
else
1)
else
(if i.val < 1867 then
1
else
0))
else
(if i.val < 1870 then
(if i.val < 1869 then
0
else
1)
else
(if i.val < 1871 then
0
else
(if i.val < 1872 then
1
else
0)))))
else
(if i.val < 1881 then
(if i.val < 1877 then
(if i.val < 1875 then
(if i.val < 1874 then
1
else
1)
else
(if i.val < 1876 then
0
else
1))
else
(if i.val < 1879 then
(if i.val < 1878 then
0
else
1)
else
(if i.val < 1880 then
0
else
1)))
else
(if i.val < 1885 then
(if i.val < 1883 then
(if i.val < 1882 then
1
else
0)
else
(if i.val < 1884 then
1
else
1))
else
(if i.val < 1887 then
(if i.val < 1886 then
1
else
0)
else
(if i.val < 1888 then
1
else
(if i.val < 1889 then
0
else
1)))))))))
else
(if i.val < 2025 then
(if i.val < 1957 then
(if i.val < 1923 then
(if i.val < 1906 then
(if i.val < 1898 then
(if i.val < 1894 then
(if i.val < 1892 then
(if i.val < 1891 then
1
else
0)
else
(if i.val < 1893 then
1
else
1))
else
(if i.val < 1896 then
(if i.val < 1895 then
1
else
0)
else
(if i.val < 1897 then
1
else
0)))
else
(if i.val < 1902 then
(if i.val < 1900 then
(if i.val < 1899 then
1
else
0)
else
(if i.val < 1901 then
1
else
0))
else
(if i.val < 1904 then
(if i.val < 1903 then
1
else
0)
else
(if i.val < 1905 then
1
else
1))))
else
(if i.val < 1914 then
(if i.val < 1910 then
(if i.val < 1908 then
(if i.val < 1907 then
0
else
1)
else
(if i.val < 1909 then
1
else
1))
else
(if i.val < 1912 then
(if i.val < 1911 then
1
else
0)
else
(if i.val < 1913 then
1
else
0)))
else
(if i.val < 1918 then
(if i.val < 1916 then
(if i.val < 1915 then
1
else
0)
else
(if i.val < 1917 then
1
else
0))
else
(if i.val < 1920 then
(if i.val < 1919 then
1
else
0)
else
(if i.val < 1921 then
1
else
(if i.val < 1922 then
0
else
1))))))
else
(if i.val < 1940 then
(if i.val < 1931 then
(if i.val < 1927 then
(if i.val < 1925 then
(if i.val < 1924 then
0
else
1)
else
(if i.val < 1926 then
0
else
1))
else
(if i.val < 1929 then
(if i.val < 1928 then
1
else
0)
else
(if i.val < 1930 then
1
else
0)))
else
(if i.val < 1935 then
(if i.val < 1933 then
(if i.val < 1932 then
1
else
1)
else
(if i.val < 1934 then
1
else
0))
else
(if i.val < 1937 then
(if i.val < 1936 then
1
else
0)
else
(if i.val < 1938 then
1
else
(if i.val < 1939 then
1
else
1)))))
else
(if i.val < 1948 then
(if i.val < 1944 then
(if i.val < 1942 then
(if i.val < 1941 then
1
else
1)
else
(if i.val < 1943 then
0
else
1))
else
(if i.val < 1946 then
(if i.val < 1945 then
1
else
0)
else
(if i.val < 1947 then
1
else
0)))
else
(if i.val < 1952 then
(if i.val < 1950 then
(if i.val < 1949 then
1
else
0)
else
(if i.val < 1951 then
1
else
1))
else
(if i.val < 1954 then
(if i.val < 1953 then
0
else
1)
else
(if i.val < 1955 then
1
else
(if i.val < 1956 then
0
else
1)))))))
else
(if i.val < 1991 then
(if i.val < 1974 then
(if i.val < 1965 then
(if i.val < 1961 then
(if i.val < 1959 then
(if i.val < 1958 then
0
else
1)
else
(if i.val < 1960 then
1
else
1))
else
(if i.val < 1963 then
(if i.val < 1962 then
1
else
1)
else
(if i.val < 1964 then
0
else
1)))
else
(if i.val < 1969 then
(if i.val < 1967 then
(if i.val < 1966 then
0
else
0)
else
(if i.val < 1968 then
0
else
1))
else
(if i.val < 1971 then
(if i.val < 1970 then
1
else
0)
else
(if i.val < 1972 then
0
else
(if i.val < 1973 then
1
else
0)))))
else
(if i.val < 1982 then
(if i.val < 1978 then
(if i.val < 1976 then
(if i.val < 1975 then
0
else
1)
else
(if i.val < 1977 then
0
else
1))
else
(if i.val < 1980 then
(if i.val < 1979 then
0
else
0)
else
(if i.val < 1981 then
1
else
0)))
else
(if i.val < 1986 then
(if i.val < 1984 then
(if i.val < 1983 then
1
else
1)
else
(if i.val < 1985 then
0
else
1))
else
(if i.val < 1988 then
(if i.val < 1987 then
0
else
1)
else
(if i.val < 1989 then
0
else
(if i.val < 1990 then
1
else
1))))))
else
(if i.val < 2008 then
(if i.val < 1999 then
(if i.val < 1995 then
(if i.val < 1993 then
(if i.val < 1992 then
0
else
1)
else
(if i.val < 1994 then
0
else
1))
else
(if i.val < 1997 then
(if i.val < 1996 then
0
else
1)
else
(if i.val < 1998 then
0
else
1)))
else
(if i.val < 2003 then
(if i.val < 2001 then
(if i.val < 2000 then
0
else
1)
else
(if i.val < 2002 then
1
else
0))
else
(if i.val < 2005 then
(if i.val < 2004 then
1
else
0)
else
(if i.val < 2006 then
0
else
(if i.val < 2007 then
1
else
0)))))
else
(if i.val < 2016 then
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
0
else
0)
else
(if i.val < 2011 then
1
else
0))
else
(if i.val < 2014 then
(if i.val < 2013 then
1
else
0)
else
(if i.val < 2015 then
1
else
0)))
else
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
1
else
1)
else
(if i.val < 2019 then
0
else
1))
else
(if i.val < 2022 then
(if i.val < 2021 then
0
else
1)
else
(if i.val < 2023 then
0
else
(if i.val < 2024 then
1
else
1))))))))
else
(if i.val < 2092 then
(if i.val < 2058 then
(if i.val < 2041 then
(if i.val < 2033 then
(if i.val < 2029 then
(if i.val < 2027 then
(if i.val < 2026 then
1
else
1)
else
(if i.val < 2028 then
0
else
0))
else
(if i.val < 2031 then
(if i.val < 2030 then
1
else
0)
else
(if i.val < 2032 then
1
else
1)))
else
(if i.val < 2037 then
(if i.val < 2035 then
(if i.val < 2034 then
0
else
1)
else
(if i.val < 2036 then
0
else
1))
else
(if i.val < 2039 then
(if i.val < 2038 then
1
else
0)
else
(if i.val < 2040 then
1
else
0))))
else
(if i.val < 2049 then
(if i.val < 2045 then
(if i.val < 2043 then
(if i.val < 2042 then
1
else
1)
else
(if i.val < 2044 then
1
else
0))
else
(if i.val < 2047 then
(if i.val < 2046 then
1
else
0)
else
(if i.val < 2048 then
1
else
0)))
else
(if i.val < 2053 then
(if i.val < 2051 then
(if i.val < 2050 then
1
else
1)
else
(if i.val < 2052 then
1
else
0))
else
(if i.val < 2055 then
(if i.val < 2054 then
1
else
1)
else
(if i.val < 2056 then
0
else
(if i.val < 2057 then
1
else
1))))))
else
(if i.val < 2075 then
(if i.val < 2066 then
(if i.val < 2062 then
(if i.val < 2060 then
(if i.val < 2059 then
0
else
1)
else
(if i.val < 2061 then
1
else
0))
else
(if i.val < 2064 then
(if i.val < 2063 then
1
else
0)
else
(if i.val < 2065 then
0
else
1)))
else
(if i.val < 2070 then
(if i.val < 2068 then
(if i.val < 2067 then
0
else
1)
else
(if i.val < 2069 then
1
else
0))
else
(if i.val < 2072 then
(if i.val < 2071 then
1
else
0)
else
(if i.val < 2073 then
1
else
(if i.val < 2074 then
1
else
1)))))
else
(if i.val < 2083 then
(if i.val < 2079 then
(if i.val < 2077 then
(if i.val < 2076 then
1
else
0)
else
(if i.val < 2078 then
1
else
0))
else
(if i.val < 2081 then
(if i.val < 2080 then
0
else
1)
else
(if i.val < 2082 then
1
else
1)))
else
(if i.val < 2087 then
(if i.val < 2085 then
(if i.val < 2084 then
0
else
0)
else
(if i.val < 2086 then
1
else
0))
else
(if i.val < 2089 then
(if i.val < 2088 then
1
else
0)
else
(if i.val < 2090 then
1
else
(if i.val < 2091 then
0
else
1)))))))
else
(if i.val < 2126 then
(if i.val < 2109 then
(if i.val < 2100 then
(if i.val < 2096 then
(if i.val < 2094 then
(if i.val < 2093 then
1
else
0)
else
(if i.val < 2095 then
1
else
1))
else
(if i.val < 2098 then
(if i.val < 2097 then
0
else
1)
else
(if i.val < 2099 then
1
else
0)))
else
(if i.val < 2104 then
(if i.val < 2102 then
(if i.val < 2101 then
1
else
1)
else
(if i.val < 2103 then
1
else
0))
else
(if i.val < 2106 then
(if i.val < 2105 then
1
else
1)
else
(if i.val < 2107 then
0
else
(if i.val < 2108 then
0
else
1)))))
else
(if i.val < 2117 then
(if i.val < 2113 then
(if i.val < 2111 then
(if i.val < 2110 then
0
else
1)
else
(if i.val < 2112 then
0
else
1))
else
(if i.val < 2115 then
(if i.val < 2114 then
1
else
0)
else
(if i.val < 2116 then
1
else
0)))
else
(if i.val < 2121 then
(if i.val < 2119 then
(if i.val < 2118 then
1
else
0)
else
(if i.val < 2120 then
0
else
0))
else
(if i.val < 2123 then
(if i.val < 2122 then
1
else
0)
else
(if i.val < 2124 then
1
else
(if i.val < 2125 then
1
else
1))))))
else
(if i.val < 2143 then
(if i.val < 2134 then
(if i.val < 2130 then
(if i.val < 2128 then
(if i.val < 2127 then
0
else
0)
else
(if i.val < 2129 then
1
else
0))
else
(if i.val < 2132 then
(if i.val < 2131 then
1
else
1)
else
(if i.val < 2133 then
1
else
0)))
else
(if i.val < 2138 then
(if i.val < 2136 then
(if i.val < 2135 then
1
else
0)
else
(if i.val < 2137 then
1
else
0))
else
(if i.val < 2140 then
(if i.val < 2139 then
1
else
0)
else
(if i.val < 2141 then
0
else
(if i.val < 2142 then
1
else
1)))))
else
(if i.val < 2151 then
(if i.val < 2147 then
(if i.val < 2145 then
(if i.val < 2144 then
0
else
1)
else
(if i.val < 2146 then
1
else
1))
else
(if i.val < 2149 then
(if i.val < 2148 then
0
else
1)
else
(if i.val < 2150 then
0
else
1)))
else
(if i.val < 2155 then
(if i.val < 2153 then
(if i.val < 2152 then
1
else
0)
else
(if i.val < 2154 then
1
else
0))
else
(if i.val < 2157 then
(if i.val < 2156 then
1
else
1)
else
(if i.val < 2158 then
0
else
(if i.val < 2159 then
1
else
1))))))))))))
else
(if i.val < 3240 then
(if i.val < 2700 then
(if i.val < 2430 then
(if i.val < 2295 then
(if i.val < 2227 then
(if i.val < 2193 then
(if i.val < 2176 then
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
0
else
1)
else
(if i.val < 2163 then
0
else
0))
else
(if i.val < 2166 then
(if i.val < 2165 then
1
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
1
else
0)
else
(if i.val < 2171 then
1
else
0))
else
(if i.val < 2174 then
(if i.val < 2173 then
1
else
1)
else
(if i.val < 2175 then
1
else
0))))
else
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
1
else
0)
else
(if i.val < 2179 then
1
else
1))
else
(if i.val < 2182 then
(if i.val < 2181 then
1
else
1)
else
(if i.val < 2183 then
0
else
1)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
1
else
0)
else
(if i.val < 2187 then
1
else
1))
else
(if i.val < 2190 then
(if i.val < 2189 then
1
else
1)
else
(if i.val < 2191 then
0
else
(if i.val < 2192 then
1
else
1))))))
else
(if i.val < 2210 then
(if i.val < 2201 then
(if i.val < 2197 then
(if i.val < 2195 then
(if i.val < 2194 then
1
else
0)
else
(if i.val < 2196 then
0
else
0))
else
(if i.val < 2199 then
(if i.val < 2198 then
1
else
0)
else
(if i.val < 2200 then
1
else
1)))
else
(if i.val < 2205 then
(if i.val < 2203 then
(if i.val < 2202 then
1
else
0)
else
(if i.val < 2204 then
1
else
0))
else
(if i.val < 2207 then
(if i.val < 2206 then
1
else
1)
else
(if i.val < 2208 then
0
else
(if i.val < 2209 then
1
else
1)))))
else
(if i.val < 2218 then
(if i.val < 2214 then
(if i.val < 2212 then
(if i.val < 2211 then
0
else
1)
else
(if i.val < 2213 then
1
else
0))
else
(if i.val < 2216 then
(if i.val < 2215 then
1
else
1)
else
(if i.val < 2217 then
0
else
1)))
else
(if i.val < 2222 then
(if i.val < 2220 then
(if i.val < 2219 then
1
else
0)
else
(if i.val < 2221 then
1
else
1))
else
(if i.val < 2224 then
(if i.val < 2223 then
1
else
0)
else
(if i.val < 2225 then
1
else
(if i.val < 2226 then
1
else
0)))))))
else
(if i.val < 2261 then
(if i.val < 2244 then
(if i.val < 2235 then
(if i.val < 2231 then
(if i.val < 2229 then
(if i.val < 2228 then
1
else
0)
else
(if i.val < 2230 then
1
else
0))
else
(if i.val < 2233 then
(if i.val < 2232 then
1
else
1)
else
(if i.val < 2234 then
1
else
0)))
else
(if i.val < 2239 then
(if i.val < 2237 then
(if i.val < 2236 then
0
else
1)
else
(if i.val < 2238 then
1
else
0))
else
(if i.val < 2241 then
(if i.val < 2240 then
1
else
0)
else
(if i.val < 2242 then
1
else
(if i.val < 2243 then
0
else
1)))))
else
(if i.val < 2252 then
(if i.val < 2248 then
(if i.val < 2246 then
(if i.val < 2245 then
1
else
1)
else
(if i.val < 2247 then
0
else
0))
else
(if i.val < 2250 then
(if i.val < 2249 then
1
else
1)
else
(if i.val < 2251 then
0
else
1)))
else
(if i.val < 2256 then
(if i.val < 2254 then
(if i.val < 2253 then
0
else
1)
else
(if i.val < 2255 then
0
else
1))
else
(if i.val < 2258 then
(if i.val < 2257 then
1
else
1)
else
(if i.val < 2259 then
0
else
(if i.val < 2260 then
1
else
1))))))
else
(if i.val < 2278 then
(if i.val < 2269 then
(if i.val < 2265 then
(if i.val < 2263 then
(if i.val < 2262 then
0
else
1)
else
(if i.val < 2264 then
0
else
1))
else
(if i.val < 2267 then
(if i.val < 2266 then
1
else
0)
else
(if i.val < 2268 then
1
else
0)))
else
(if i.val < 2273 then
(if i.val < 2271 then
(if i.val < 2270 then
1
else
1)
else
(if i.val < 2272 then
0
else
0))
else
(if i.val < 2275 then
(if i.val < 2274 then
1
else
0)
else
(if i.val < 2276 then
1
else
(if i.val < 2277 then
0
else
1)))))
else
(if i.val < 2286 then
(if i.val < 2282 then
(if i.val < 2280 then
(if i.val < 2279 then
0
else
0)
else
(if i.val < 2281 then
1
else
0))
else
(if i.val < 2284 then
(if i.val < 2283 then
1
else
1)
else
(if i.val < 2285 then
0
else
0)))
else
(if i.val < 2290 then
(if i.val < 2288 then
(if i.val < 2287 then
1
else
0)
else
(if i.val < 2289 then
1
else
0))
else
(if i.val < 2292 then
(if i.val < 2291 then
1
else
1)
else
(if i.val < 2293 then
0
else
(if i.val < 2294 then
1
else
0))))))))
else
(if i.val < 2362 then
(if i.val < 2328 then
(if i.val < 2311 then
(if i.val < 2303 then
(if i.val < 2299 then
(if i.val < 2297 then
(if i.val < 2296 then
1
else
0)
else
(if i.val < 2298 then
1
else
1))
else
(if i.val < 2301 then
(if i.val < 2300 then
0
else
1)
else
(if i.val < 2302 then
0
else
0)))
else
(if i.val < 2307 then
(if i.val < 2305 then
(if i.val < 2304 then
1
else
0)
else
(if i.val < 2306 then
1
else
1))
else
(if i.val < 2309 then
(if i.val < 2308 then
0
else
1)
else
(if i.val < 2310 then
0
else
0))))
else
(if i.val < 2319 then
(if i.val < 2315 then
(if i.val < 2313 then
(if i.val < 2312 then
1
else
1)
else
(if i.val < 2314 then
1
else
0))
else
(if i.val < 2317 then
(if i.val < 2316 then
1
else
0)
else
(if i.val < 2318 then
1
else
0)))
else
(if i.val < 2323 then
(if i.val < 2321 then
(if i.val < 2320 then
1
else
0)
else
(if i.val < 2322 then
1
else
1))
else
(if i.val < 2325 then
(if i.val < 2324 then
0
else
1)
else
(if i.val < 2326 then
0
else
(if i.val < 2327 then
0
else
0))))))
else
(if i.val < 2345 then
(if i.val < 2336 then
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
1
else
1)
else
(if i.val < 2331 then
0
else
1))
else
(if i.val < 2334 then
(if i.val < 2333 then
0
else
1)
else
(if i.val < 2335 then
1
else
0)))
else
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
1
else
0)
else
(if i.val < 2339 then
1
else
0))
else
(if i.val < 2342 then
(if i.val < 2341 then
1
else
1)
else
(if i.val < 2343 then
1
else
(if i.val < 2344 then
0
else
0)))))
else
(if i.val < 2353 then
(if i.val < 2349 then
(if i.val < 2347 then
(if i.val < 2346 then
1
else
0)
else
(if i.val < 2348 then
1
else
0))
else
(if i.val < 2351 then
(if i.val < 2350 then
1
else
0)
else
(if i.val < 2352 then
0
else
1)))
else
(if i.val < 2357 then
(if i.val < 2355 then
(if i.val < 2354 then
0
else
1)
else
(if i.val < 2356 then
0
else
1))
else
(if i.val < 2359 then
(if i.val < 2358 then
0
else
1)
else
(if i.val < 2360 then
0
else
(if i.val < 2361 then
0
else
1)))))))
else
(if i.val < 2396 then
(if i.val < 2379 then
(if i.val < 2370 then
(if i.val < 2366 then
(if i.val < 2364 then
(if i.val < 2363 then
1
else
0)
else
(if i.val < 2365 then
1
else
1))
else
(if i.val < 2368 then
(if i.val < 2367 then
1
else
1)
else
(if i.val < 2369 then
0
else
1)))
else
(if i.val < 2374 then
(if i.val < 2372 then
(if i.val < 2371 then
0
else
1)
else
(if i.val < 2373 then
1
else
1))
else
(if i.val < 2376 then
(if i.val < 2375 then
0
else
1)
else
(if i.val < 2377 then
1
else
(if i.val < 2378 then
0
else
1)))))
else
(if i.val < 2387 then
(if i.val < 2383 then
(if i.val < 2381 then
(if i.val < 2380 then
0
else
1)
else
(if i.val < 2382 then
0
else
0))
else
(if i.val < 2385 then
(if i.val < 2384 then
1
else
0)
else
(if i.val < 2386 then
1
else
1)))
else
(if i.val < 2391 then
(if i.val < 2389 then
(if i.val < 2388 then
0
else
1)
else
(if i.val < 2390 then
1
else
0))
else
(if i.val < 2393 then
(if i.val < 2392 then
1
else
0)
else
(if i.val < 2394 then
1
else
(if i.val < 2395 then
0
else
0))))))
else
(if i.val < 2413 then
(if i.val < 2404 then
(if i.val < 2400 then
(if i.val < 2398 then
(if i.val < 2397 then
1
else
1)
else
(if i.val < 2399 then
1
else
0))
else
(if i.val < 2402 then
(if i.val < 2401 then
1
else
1)
else
(if i.val < 2403 then
0
else
1)))
else
(if i.val < 2408 then
(if i.val < 2406 then
(if i.val < 2405 then
0
else
1)
else
(if i.val < 2407 then
1
else
1))
else
(if i.val < 2410 then
(if i.val < 2409 then
0
else
1)
else
(if i.val < 2411 then
0
else
(if i.val < 2412 then
1
else
1)))))
else
(if i.val < 2421 then
(if i.val < 2417 then
(if i.val < 2415 then
(if i.val < 2414 then
1
else
1)
else
(if i.val < 2416 then
0
else
1))
else
(if i.val < 2419 then
(if i.val < 2418 then
0
else
1)
else
(if i.val < 2420 then
0
else
1)))
else
(if i.val < 2425 then
(if i.val < 2423 then
(if i.val < 2422 then
1
else
0)
else
(if i.val < 2424 then
1
else
0))
else
(if i.val < 2427 then
(if i.val < 2426 then
1
else
1)
else
(if i.val < 2428 then
0
else
(if i.val < 2429 then
1
else
0)))))))))
else
(if i.val < 2565 then
(if i.val < 2497 then
(if i.val < 2463 then
(if i.val < 2446 then
(if i.val < 2438 then
(if i.val < 2434 then
(if i.val < 2432 then
(if i.val < 2431 then
1
else
1)
else
(if i.val < 2433 then
0
else
1))
else
(if i.val < 2436 then
(if i.val < 2435 then
0
else
1)
else
(if i.val < 2437 then
0
else
1)))
else
(if i.val < 2442 then
(if i.val < 2440 then
(if i.val < 2439 then
0
else
0)
else
(if i.val < 2441 then
1
else
1))
else
(if i.val < 2444 then
(if i.val < 2443 then
0
else
1)
else
(if i.val < 2445 then
0
else
1))))
else
(if i.val < 2454 then
(if i.val < 2450 then
(if i.val < 2448 then
(if i.val < 2447 then
1
else
0)
else
(if i.val < 2449 then
1
else
1))
else
(if i.val < 2452 then
(if i.val < 2451 then
1
else
1)
else
(if i.val < 2453 then
1
else
0)))
else
(if i.val < 2458 then
(if i.val < 2456 then
(if i.val < 2455 then
1
else
1)
else
(if i.val < 2457 then
0
else
1))
else
(if i.val < 2460 then
(if i.val < 2459 then
0
else
1)
else
(if i.val < 2461 then
0
else
(if i.val < 2462 then
1
else
0))))))
else
(if i.val < 2480 then
(if i.val < 2471 then
(if i.val < 2467 then
(if i.val < 2465 then
(if i.val < 2464 then
1
else
1)
else
(if i.val < 2466 then
1
else
0))
else
(if i.val < 2469 then
(if i.val < 2468 then
0
else
1)
else
(if i.val < 2470 then
0
else
1)))
else
(if i.val < 2475 then
(if i.val < 2473 then
(if i.val < 2472 then
0
else
1)
else
(if i.val < 2474 then
1
else
0))
else
(if i.val < 2477 then
(if i.val < 2476 then
1
else
0)
else
(if i.val < 2478 then
1
else
(if i.val < 2479 then
1
else
1)))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
1
else
1)
else
(if i.val < 2483 then
0
else
1))
else
(if i.val < 2486 then
(if i.val < 2485 then
0
else
1)
else
(if i.val < 2487 then
1
else
0)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
1
else
1)
else
(if i.val < 2491 then
1
else
0))
else
(if i.val < 2494 then
(if i.val < 2493 then
1
else
0)
else
(if i.val < 2495 then
0
else
(if i.val < 2496 then
1
else
0)))))))
else
(if i.val < 2531 then
(if i.val < 2514 then
(if i.val < 2505 then
(if i.val < 2501 then
(if i.val < 2499 then
(if i.val < 2498 then
1
else
1)
else
(if i.val < 2500 then
1
else
1))
else
(if i.val < 2503 then
(if i.val < 2502 then
1
else
0)
else
(if i.val < 2504 then
0
else
1)))
else
(if i.val < 2509 then
(if i.val < 2507 then
(if i.val < 2506 then
0
else
1)
else
(if i.val < 2508 then
0
else
1))
else
(if i.val < 2511 then
(if i.val < 2510 then
0
else
1)
else
(if i.val < 2512 then
0
else
(if i.val < 2513 then
1
else
1)))))
else
(if i.val < 2522 then
(if i.val < 2518 then
(if i.val < 2516 then
(if i.val < 2515 then
0
else
1)
else
(if i.val < 2517 then
0
else
1))
else
(if i.val < 2520 then
(if i.val < 2519 then
1
else
1)
else
(if i.val < 2521 then
1
else
1)))
else
(if i.val < 2526 then
(if i.val < 2524 then
(if i.val < 2523 then
1
else
1)
else
(if i.val < 2525 then
0
else
1))
else
(if i.val < 2528 then
(if i.val < 2527 then
1
else
0)
else
(if i.val < 2529 then
1
else
(if i.val < 2530 then
0
else
1))))))
else
(if i.val < 2548 then
(if i.val < 2539 then
(if i.val < 2535 then
(if i.val < 2533 then
(if i.val < 2532 then
0
else
1)
else
(if i.val < 2534 then
0
else
1))
else
(if i.val < 2537 then
(if i.val < 2536 then
0
else
1)
else
(if i.val < 2538 then
0
else
1)))
else
(if i.val < 2543 then
(if i.val < 2541 then
(if i.val < 2540 then
1
else
1)
else
(if i.val < 2542 then
0
else
1))
else
(if i.val < 2545 then
(if i.val < 2544 then
0
else
0)
else
(if i.val < 2546 then
1
else
(if i.val < 2547 then
0
else
0)))))
else
(if i.val < 2556 then
(if i.val < 2552 then
(if i.val < 2550 then
(if i.val < 2549 then
0
else
1)
else
(if i.val < 2551 then
1
else
0))
else
(if i.val < 2554 then
(if i.val < 2553 then
0
else
1)
else
(if i.val < 2555 then
0
else
1)))
else
(if i.val < 2560 then
(if i.val < 2558 then
(if i.val < 2557 then
1
else
0)
else
(if i.val < 2559 then
0
else
1))
else
(if i.val < 2562 then
(if i.val < 2561 then
0
else
0)
else
(if i.val < 2563 then
1
else
(if i.val < 2564 then
0
else
0))))))))
else
(if i.val < 2632 then
(if i.val < 2598 then
(if i.val < 2581 then
(if i.val < 2573 then
(if i.val < 2569 then
(if i.val < 2567 then
(if i.val < 2566 then
0
else
0)
else
(if i.val < 2568 then
1
else
1))
else
(if i.val < 2571 then
(if i.val < 2570 then
0
else
1)
else
(if i.val < 2572 then
0
else
1)))
else
(if i.val < 2577 then
(if i.val < 2575 then
(if i.val < 2574 then
1
else
0)
else
(if i.val < 2576 then
1
else
1))
else
(if i.val < 2579 then
(if i.val < 2578 then
0
else
1)
else
(if i.val < 2580 then
0
else
0))))
else
(if i.val < 2589 then
(if i.val < 2585 then
(if i.val < 2583 then
(if i.val < 2582 then
1
else
1)
else
(if i.val < 2584 then
1
else
0))
else
(if i.val < 2587 then
(if i.val < 2586 then
1
else
1)
else
(if i.val < 2588 then
0
else
1)))
else
(if i.val < 2593 then
(if i.val < 2591 then
(if i.val < 2590 then
0
else
1)
else
(if i.val < 2592 then
0
else
1))
else
(if i.val < 2595 then
(if i.val < 2594 then
0
else
0)
else
(if i.val < 2596 then
1
else
(if i.val < 2597 then
1
else
0))))))
else
(if i.val < 2615 then
(if i.val < 2606 then
(if i.val < 2602 then
(if i.val < 2600 then
(if i.val < 2599 then
1
else
0)
else
(if i.val < 2601 then
1
else
0))
else
(if i.val < 2604 then
(if i.val < 2603 then
1
else
0)
else
(if i.val < 2605 then
1
else
0)))
else
(if i.val < 2610 then
(if i.val < 2608 then
(if i.val < 2607 then
1
else
0)
else
(if i.val < 2609 then
0
else
1))
else
(if i.val < 2612 then
(if i.val < 2611 then
1
else
0)
else
(if i.val < 2613 then
1
else
(if i.val < 2614 then
0
else
1)))))
else
(if i.val < 2623 then
(if i.val < 2619 then
(if i.val < 2617 then
(if i.val < 2616 then
0
else
1)
else
(if i.val < 2618 then
0
else
0))
else
(if i.val < 2621 then
(if i.val < 2620 then
0
else
1)
else
(if i.val < 2622 then
1
else
1)))
else
(if i.val < 2627 then
(if i.val < 2625 then
(if i.val < 2624 then
0
else
0)
else
(if i.val < 2626 then
0
else
1))
else
(if i.val < 2629 then
(if i.val < 2628 then
0
else
1)
else
(if i.val < 2630 then
0
else
(if i.val < 2631 then
1
else
0)))))))
else
(if i.val < 2666 then
(if i.val < 2649 then
(if i.val < 2640 then
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
0
else
1)
else
(if i.val < 2635 then
1
else
0))
else
(if i.val < 2638 then
(if i.val < 2637 then
1
else
0)
else
(if i.val < 2639 then
1
else
1)))
else
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
0
else
1)
else
(if i.val < 2643 then
0
else
1))
else
(if i.val < 2646 then
(if i.val < 2645 then
0
else
0)
else
(if i.val < 2647 then
1
else
(if i.val < 2648 then
1
else
1)))))
else
(if i.val < 2657 then
(if i.val < 2653 then
(if i.val < 2651 then
(if i.val < 2650 then
0
else
1)
else
(if i.val < 2652 then
0
else
1))
else
(if i.val < 2655 then
(if i.val < 2654 then
1
else
0)
else
(if i.val < 2656 then
1
else
0)))
else
(if i.val < 2661 then
(if i.val < 2659 then
(if i.val < 2658 then
1
else
1)
else
(if i.val < 2660 then
0
else
1))
else
(if i.val < 2663 then
(if i.val < 2662 then
1
else
1)
else
(if i.val < 2664 then
0
else
(if i.val < 2665 then
1
else
1))))))
else
(if i.val < 2683 then
(if i.val < 2674 then
(if i.val < 2670 then
(if i.val < 2668 then
(if i.val < 2667 then
0
else
1)
else
(if i.val < 2669 then
0
else
1))
else
(if i.val < 2672 then
(if i.val < 2671 then
1
else
0)
else
(if i.val < 2673 then
0
else
1)))
else
(if i.val < 2678 then
(if i.val < 2676 then
(if i.val < 2675 then
1
else
0)
else
(if i.val < 2677 then
1
else
1))
else
(if i.val < 2680 then
(if i.val < 2679 then
1
else
1)
else
(if i.val < 2681 then
0
else
(if i.val < 2682 then
1
else
0)))))
else
(if i.val < 2691 then
(if i.val < 2687 then
(if i.val < 2685 then
(if i.val < 2684 then
1
else
0)
else
(if i.val < 2686 then
1
else
0))
else
(if i.val < 2689 then
(if i.val < 2688 then
0
else
0)
else
(if i.val < 2690 then
1
else
1)))
else
(if i.val < 2695 then
(if i.val < 2693 then
(if i.val < 2692 then
0
else
1)
else
(if i.val < 2694 then
0
else
0))
else
(if i.val < 2697 then
(if i.val < 2696 then
1
else
0)
else
(if i.val < 2698 then
1
else
(if i.val < 2699 then
1
else
0))))))))))
else
(if i.val < 2970 then
(if i.val < 2835 then
(if i.val < 2767 then
(if i.val < 2733 then
(if i.val < 2716 then
(if i.val < 2708 then
(if i.val < 2704 then
(if i.val < 2702 then
(if i.val < 2701 then
1
else
1)
else
(if i.val < 2703 then
0
else
1))
else
(if i.val < 2706 then
(if i.val < 2705 then
0
else
1)
else
(if i.val < 2707 then
0
else
0)))
else
(if i.val < 2712 then
(if i.val < 2710 then
(if i.val < 2709 then
1
else
0)
else
(if i.val < 2711 then
1
else
1))
else
(if i.val < 2714 then
(if i.val < 2713 then
0
else
1)
else
(if i.val < 2715 then
0
else
0))))
else
(if i.val < 2724 then
(if i.val < 2720 then
(if i.val < 2718 then
(if i.val < 2717 then
1
else
0)
else
(if i.val < 2719 then
1
else
1))
else
(if i.val < 2722 then
(if i.val < 2721 then
1
else
1)
else
(if i.val < 2723 then
1
else
0)))
else
(if i.val < 2728 then
(if i.val < 2726 then
(if i.val < 2725 then
1
else
0)
else
(if i.val < 2727 then
1
else
0))
else
(if i.val < 2730 then
(if i.val < 2729 then
1
else
1)
else
(if i.val < 2731 then
0
else
(if i.val < 2732 then
1
else
0))))))
else
(if i.val < 2750 then
(if i.val < 2741 then
(if i.val < 2737 then
(if i.val < 2735 then
(if i.val < 2734 then
0
else
1)
else
(if i.val < 2736 then
1
else
1))
else
(if i.val < 2739 then
(if i.val < 2738 then
1
else
0)
else
(if i.val < 2740 then
1
else
0)))
else
(if i.val < 2745 then
(if i.val < 2743 then
(if i.val < 2742 then
1
else
0)
else
(if i.val < 2744 then
1
else
1))
else
(if i.val < 2747 then
(if i.val < 2746 then
1
else
1)
else
(if i.val < 2748 then
0
else
(if i.val < 2749 then
1
else
0)))))
else
(if i.val < 2758 then
(if i.val < 2754 then
(if i.val < 2752 then
(if i.val < 2751 then
1
else
1)
else
(if i.val < 2753 then
0
else
1))
else
(if i.val < 2756 then
(if i.val < 2755 then
0
else
0)
else
(if i.val < 2757 then
1
else
0)))
else
(if i.val < 2762 then
(if i.val < 2760 then
(if i.val < 2759 then
0
else
1)
else
(if i.val < 2761 then
1
else
0))
else
(if i.val < 2764 then
(if i.val < 2763 then
0
else
1)
else
(if i.val < 2765 then
0
else
(if i.val < 2766 then
1
else
0)))))))
else
(if i.val < 2801 then
(if i.val < 2784 then
(if i.val < 2775 then
(if i.val < 2771 then
(if i.val < 2769 then
(if i.val < 2768 then
0
else
0)
else
(if i.val < 2770 then
1
else
1))
else
(if i.val < 2773 then
(if i.val < 2772 then
0
else
0)
else
(if i.val < 2774 then
1
else
1)))
else
(if i.val < 2779 then
(if i.val < 2777 then
(if i.val < 2776 then
0
else
1)
else
(if i.val < 2778 then
0
else
1))
else
(if i.val < 2781 then
(if i.val < 2780 then
0
else
1)
else
(if i.val < 2782 then
0
else
(if i.val < 2783 then
1
else
0)))))
else
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
1
else
1)
else
(if i.val < 2787 then
0
else
1))
else
(if i.val < 2790 then
(if i.val < 2789 then
0
else
1)
else
(if i.val < 2791 then
1
else
0)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
0
else
1)
else
(if i.val < 2795 then
0
else
1))
else
(if i.val < 2798 then
(if i.val < 2797 then
1
else
0)
else
(if i.val < 2799 then
1
else
(if i.val < 2800 then
0
else
1))))))
else
(if i.val < 2818 then
(if i.val < 2809 then
(if i.val < 2805 then
(if i.val < 2803 then
(if i.val < 2802 then
0
else
1)
else
(if i.val < 2804 then
0
else
1))
else
(if i.val < 2807 then
(if i.val < 2806 then
0
else
1)
else
(if i.val < 2808 then
1
else
0)))
else
(if i.val < 2813 then
(if i.val < 2811 then
(if i.val < 2810 then
1
else
1)
else
(if i.val < 2812 then
0
else
1))
else
(if i.val < 2815 then
(if i.val < 2814 then
0
else
1)
else
(if i.val < 2816 then
0
else
(if i.val < 2817 then
1
else
1)))))
else
(if i.val < 2826 then
(if i.val < 2822 then
(if i.val < 2820 then
(if i.val < 2819 then
0
else
0)
else
(if i.val < 2821 then
0
else
1))
else
(if i.val < 2824 then
(if i.val < 2823 then
0
else
1)
else
(if i.val < 2825 then
0
else
1)))
else
(if i.val < 2830 then
(if i.val < 2828 then
(if i.val < 2827 then
0
else
0)
else
(if i.val < 2829 then
0
else
0))
else
(if i.val < 2832 then
(if i.val < 2831 then
1
else
0)
else
(if i.val < 2833 then
0
else
(if i.val < 2834 then
0
else
0))))))))
else
(if i.val < 2902 then
(if i.val < 2868 then
(if i.val < 2851 then
(if i.val < 2843 then
(if i.val < 2839 then
(if i.val < 2837 then
(if i.val < 2836 then
1
else
1)
else
(if i.val < 2838 then
0
else
1))
else
(if i.val < 2841 then
(if i.val < 2840 then
1
else
1)
else
(if i.val < 2842 then
0
else
1)))
else
(if i.val < 2847 then
(if i.val < 2845 then
(if i.val < 2844 then
1
else
1)
else
(if i.val < 2846 then
1
else
0))
else
(if i.val < 2849 then
(if i.val < 2848 then
1
else
0)
else
(if i.val < 2850 then
1
else
1))))
else
(if i.val < 2859 then
(if i.val < 2855 then
(if i.val < 2853 then
(if i.val < 2852 then
0
else
1)
else
(if i.val < 2854 then
1
else
1))
else
(if i.val < 2857 then
(if i.val < 2856 then
1
else
0)
else
(if i.val < 2858 then
1
else
0)))
else
(if i.val < 2863 then
(if i.val < 2861 then
(if i.val < 2860 then
1
else
0)
else
(if i.val < 2862 then
1
else
0))
else
(if i.val < 2865 then
(if i.val < 2864 then
1
else
0)
else
(if i.val < 2866 then
1
else
(if i.val < 2867 then
1
else
1))))))
else
(if i.val < 2885 then
(if i.val < 2876 then
(if i.val < 2872 then
(if i.val < 2870 then
(if i.val < 2869 then
1
else
1)
else
(if i.val < 2871 then
0
else
1))
else
(if i.val < 2874 then
(if i.val < 2873 then
1
else
0)
else
(if i.val < 2875 then
1
else
0)))
else
(if i.val < 2880 then
(if i.val < 2878 then
(if i.val < 2877 then
1
else
1)
else
(if i.val < 2879 then
1
else
1))
else
(if i.val < 2882 then
(if i.val < 2881 then
1
else
1)
else
(if i.val < 2883 then
0
else
(if i.val < 2884 then
1
else
0)))))
else
(if i.val < 2893 then
(if i.val < 2889 then
(if i.val < 2887 then
(if i.val < 2886 then
1
else
0)
else
(if i.val < 2888 then
1
else
1))
else
(if i.val < 2891 then
(if i.val < 2890 then
0
else
1)
else
(if i.val < 2892 then
0
else
1)))
else
(if i.val < 2897 then
(if i.val < 2895 then
(if i.val < 2894 then
0
else
1)
else
(if i.val < 2896 then
1
else
1))
else
(if i.val < 2899 then
(if i.val < 2898 then
0
else
0)
else
(if i.val < 2900 then
1
else
(if i.val < 2901 then
0
else
1)))))))
else
(if i.val < 2936 then
(if i.val < 2919 then
(if i.val < 2910 then
(if i.val < 2906 then
(if i.val < 2904 then
(if i.val < 2903 then
0
else
1)
else
(if i.val < 2905 then
0
else
1))
else
(if i.val < 2908 then
(if i.val < 2907 then
0
else
1)
else
(if i.val < 2909 then
0
else
1)))
else
(if i.val < 2914 then
(if i.val < 2912 then
(if i.val < 2911 then
0
else
0)
else
(if i.val < 2913 then
1
else
1))
else
(if i.val < 2916 then
(if i.val < 2915 then
0
else
1)
else
(if i.val < 2917 then
0
else
(if i.val < 2918 then
1
else
0)))))
else
(if i.val < 2927 then
(if i.val < 2923 then
(if i.val < 2921 then
(if i.val < 2920 then
1
else
1)
else
(if i.val < 2922 then
0
else
0))
else
(if i.val < 2925 then
(if i.val < 2924 then
1
else
1)
else
(if i.val < 2926 then
1
else
0)))
else
(if i.val < 2931 then
(if i.val < 2929 then
(if i.val < 2928 then
1
else
1)
else
(if i.val < 2930 then
0
else
1))
else
(if i.val < 2933 then
(if i.val < 2932 then
0
else
1)
else
(if i.val < 2934 then
0
else
(if i.val < 2935 then
1
else
0))))))
else
(if i.val < 2953 then
(if i.val < 2944 then
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
1
else
0)
else
(if i.val < 2939 then
1
else
0))
else
(if i.val < 2942 then
(if i.val < 2941 then
1
else
1)
else
(if i.val < 2943 then
1
else
0)))
else
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
0
else
1)
else
(if i.val < 2947 then
1
else
1))
else
(if i.val < 2950 then
(if i.val < 2949 then
1
else
0)
else
(if i.val < 2951 then
1
else
(if i.val < 2952 then
1
else
0)))))
else
(if i.val < 2961 then
(if i.val < 2957 then
(if i.val < 2955 then
(if i.val < 2954 then
0
else
1)
else
(if i.val < 2956 then
1
else
0))
else
(if i.val < 2959 then
(if i.val < 2958 then
1
else
0)
else
(if i.val < 2960 then
1
else
1)))
else
(if i.val < 2965 then
(if i.val < 2963 then
(if i.val < 2962 then
1
else
0)
else
(if i.val < 2964 then
1
else
1))
else
(if i.val < 2967 then
(if i.val < 2966 then
0
else
1)
else
(if i.val < 2968 then
1
else
(if i.val < 2969 then
0
else
1)))))))))
else
(if i.val < 3105 then
(if i.val < 3037 then
(if i.val < 3003 then
(if i.val < 2986 then
(if i.val < 2978 then
(if i.val < 2974 then
(if i.val < 2972 then
(if i.val < 2971 then
0
else
1)
else
(if i.val < 2973 then
1
else
0))
else
(if i.val < 2976 then
(if i.val < 2975 then
1
else
0)
else
(if i.val < 2977 then
1
else
0)))
else
(if i.val < 2982 then
(if i.val < 2980 then
(if i.val < 2979 then
1
else
0)
else
(if i.val < 2981 then
1
else
1))
else
(if i.val < 2984 then
(if i.val < 2983 then
0
else
1)
else
(if i.val < 2985 then
1
else
0))))
else
(if i.val < 2994 then
(if i.val < 2990 then
(if i.val < 2988 then
(if i.val < 2987 then
1
else
0)
else
(if i.val < 2989 then
1
else
0))
else
(if i.val < 2992 then
(if i.val < 2991 then
1
else
0)
else
(if i.val < 2993 then
1
else
1)))
else
(if i.val < 2998 then
(if i.val < 2996 then
(if i.val < 2995 then
1
else
1)
else
(if i.val < 2997 then
0
else
0))
else
(if i.val < 3000 then
(if i.val < 2999 then
1
else
1)
else
(if i.val < 3001 then
1
else
(if i.val < 3002 then
1
else
0))))))
else
(if i.val < 3020 then
(if i.val < 3011 then
(if i.val < 3007 then
(if i.val < 3005 then
(if i.val < 3004 then
1
else
0)
else
(if i.val < 3006 then
1
else
1))
else
(if i.val < 3009 then
(if i.val < 3008 then
0
else
0)
else
(if i.val < 3010 then
1
else
1)))
else
(if i.val < 3015 then
(if i.val < 3013 then
(if i.val < 3012 then
0
else
1)
else
(if i.val < 3014 then
1
else
0))
else
(if i.val < 3017 then
(if i.val < 3016 then
1
else
1)
else
(if i.val < 3018 then
0
else
(if i.val < 3019 then
0
else
0)))))
else
(if i.val < 3028 then
(if i.val < 3024 then
(if i.val < 3022 then
(if i.val < 3021 then
1
else
0)
else
(if i.val < 3023 then
0
else
1))
else
(if i.val < 3026 then
(if i.val < 3025 then
1
else
0)
else
(if i.val < 3027 then
1
else
1)))
else
(if i.val < 3032 then
(if i.val < 3030 then
(if i.val < 3029 then
0
else
1)
else
(if i.val < 3031 then
1
else
1))
else
(if i.val < 3034 then
(if i.val < 3033 then
1
else
1)
else
(if i.val < 3035 then
1
else
(if i.val < 3036 then
0
else
0)))))))
else
(if i.val < 3071 then
(if i.val < 3054 then
(if i.val < 3045 then
(if i.val < 3041 then
(if i.val < 3039 then
(if i.val < 3038 then
0
else
1)
else
(if i.val < 3040 then
0
else
1))
else
(if i.val < 3043 then
(if i.val < 3042 then
1
else
0)
else
(if i.val < 3044 then
1
else
0)))
else
(if i.val < 3049 then
(if i.val < 3047 then
(if i.val < 3046 then
1
else
1)
else
(if i.val < 3048 then
1
else
1))
else
(if i.val < 3051 then
(if i.val < 3050 then
1
else
0)
else
(if i.val < 3052 then
1
else
(if i.val < 3053 then
0
else
1)))))
else
(if i.val < 3062 then
(if i.val < 3058 then
(if i.val < 3056 then
(if i.val < 3055 then
1
else
1)
else
(if i.val < 3057 then
0
else
0))
else
(if i.val < 3060 then
(if i.val < 3059 then
0
else
1)
else
(if i.val < 3061 then
1
else
0)))
else
(if i.val < 3066 then
(if i.val < 3064 then
(if i.val < 3063 then
1
else
1)
else
(if i.val < 3065 then
1
else
0))
else
(if i.val < 3068 then
(if i.val < 3067 then
1
else
1)
else
(if i.val < 3069 then
0
else
(if i.val < 3070 then
1
else
1))))))
else
(if i.val < 3088 then
(if i.val < 3079 then
(if i.val < 3075 then
(if i.val < 3073 then
(if i.val < 3072 then
0
else
1)
else
(if i.val < 3074 then
0
else
1))
else
(if i.val < 3077 then
(if i.val < 3076 then
0
else
1)
else
(if i.val < 3078 then
0
else
0)))
else
(if i.val < 3083 then
(if i.val < 3081 then
(if i.val < 3080 then
1
else
0)
else
(if i.val < 3082 then
1
else
0))
else
(if i.val < 3085 then
(if i.val < 3084 then
1
else
0)
else
(if i.val < 3086 then
0
else
(if i.val < 3087 then
1
else
1)))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
0
else
1)
else
(if i.val < 3091 then
0
else
0))
else
(if i.val < 3094 then
(if i.val < 3093 then
1
else
0)
else
(if i.val < 3095 then
0
else
1)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
0
else
1)
else
(if i.val < 3099 then
0
else
0))
else
(if i.val < 3102 then
(if i.val < 3101 then
1
else
1)
else
(if i.val < 3103 then
1
else
(if i.val < 3104 then
0
else
1))))))))
else
(if i.val < 3172 then
(if i.val < 3138 then
(if i.val < 3121 then
(if i.val < 3113 then
(if i.val < 3109 then
(if i.val < 3107 then
(if i.val < 3106 then
0
else
1)
else
(if i.val < 3108 then
0
else
1))
else
(if i.val < 3111 then
(if i.val < 3110 then
0
else
1)
else
(if i.val < 3112 then
1
else
0)))
else
(if i.val < 3117 then
(if i.val < 3115 then
(if i.val < 3114 then
1
else
1)
else
(if i.val < 3116 then
1
else
0))
else
(if i.val < 3119 then
(if i.val < 3118 then
1
else
1)
else
(if i.val < 3120 then
0
else
0))))
else
(if i.val < 3129 then
(if i.val < 3125 then
(if i.val < 3123 then
(if i.val < 3122 then
1
else
0)
else
(if i.val < 3124 then
1
else
0))
else
(if i.val < 3127 then
(if i.val < 3126 then
0
else
1)
else
(if i.val < 3128 then
1
else
0)))
else
(if i.val < 3133 then
(if i.val < 3131 then
(if i.val < 3130 then
1
else
1)
else
(if i.val < 3132 then
1
else
1))
else
(if i.val < 3135 then
(if i.val < 3134 then
1
else
0)
else
(if i.val < 3136 then
1
else
(if i.val < 3137 then
1
else
0))))))
else
(if i.val < 3155 then
(if i.val < 3146 then
(if i.val < 3142 then
(if i.val < 3140 then
(if i.val < 3139 then
0
else
1)
else
(if i.val < 3141 then
0
else
1))
else
(if i.val < 3144 then
(if i.val < 3143 then
1
else
1)
else
(if i.val < 3145 then
0
else
1)))
else
(if i.val < 3150 then
(if i.val < 3148 then
(if i.val < 3147 then
1
else
0)
else
(if i.val < 3149 then
1
else
0))
else
(if i.val < 3152 then
(if i.val < 3151 then
0
else
1)
else
(if i.val < 3153 then
1
else
(if i.val < 3154 then
1
else
0)))))
else
(if i.val < 3163 then
(if i.val < 3159 then
(if i.val < 3157 then
(if i.val < 3156 then
1
else
1)
else
(if i.val < 3158 then
0
else
1))
else
(if i.val < 3161 then
(if i.val < 3160 then
1
else
1)
else
(if i.val < 3162 then
1
else
1)))
else
(if i.val < 3167 then
(if i.val < 3165 then
(if i.val < 3164 then
1
else
0)
else
(if i.val < 3166 then
1
else
0))
else
(if i.val < 3169 then
(if i.val < 3168 then
1
else
0)
else
(if i.val < 3170 then
1
else
(if i.val < 3171 then
1
else
0)))))))
else
(if i.val < 3206 then
(if i.val < 3189 then
(if i.val < 3180 then
(if i.val < 3176 then
(if i.val < 3174 then
(if i.val < 3173 then
1
else
0)
else
(if i.val < 3175 then
1
else
1))
else
(if i.val < 3178 then
(if i.val < 3177 then
0
else
0)
else
(if i.val < 3179 then
0
else
1)))
else
(if i.val < 3184 then
(if i.val < 3182 then
(if i.val < 3181 then
0
else
1)
else
(if i.val < 3183 then
0
else
1))
else
(if i.val < 3186 then
(if i.val < 3185 then
1
else
1)
else
(if i.val < 3187 then
1
else
(if i.val < 3188 then
0
else
1)))))
else
(if i.val < 3197 then
(if i.val < 3193 then
(if i.val < 3191 then
(if i.val < 3190 then
0
else
1)
else
(if i.val < 3192 then
0
else
1))
else
(if i.val < 3195 then
(if i.val < 3194 then
0
else
1)
else
(if i.val < 3196 then
0
else
1)))
else
(if i.val < 3201 then
(if i.val < 3199 then
(if i.val < 3198 then
1
else
1)
else
(if i.val < 3200 then
0
else
0))
else
(if i.val < 3203 then
(if i.val < 3202 then
1
else
1)
else
(if i.val < 3204 then
0
else
(if i.val < 3205 then
1
else
0))))))
else
(if i.val < 3223 then
(if i.val < 3214 then
(if i.val < 3210 then
(if i.val < 3208 then
(if i.val < 3207 then
1
else
1)
else
(if i.val < 3209 then
1
else
0))
else
(if i.val < 3212 then
(if i.val < 3211 then
1
else
0)
else
(if i.val < 3213 then
1
else
1)))
else
(if i.val < 3218 then
(if i.val < 3216 then
(if i.val < 3215 then
1
else
0)
else
(if i.val < 3217 then
1
else
0))
else
(if i.val < 3220 then
(if i.val < 3219 then
0
else
1)
else
(if i.val < 3221 then
0
else
(if i.val < 3222 then
1
else
1)))))
else
(if i.val < 3231 then
(if i.val < 3227 then
(if i.val < 3225 then
(if i.val < 3224 then
0
else
1)
else
(if i.val < 3226 then
0
else
1))
else
(if i.val < 3229 then
(if i.val < 3228 then
0
else
1)
else
(if i.val < 3230 then
0
else
1)))
else
(if i.val < 3235 then
(if i.val < 3233 then
(if i.val < 3232 then
0
else
1)
else
(if i.val < 3234 then
1
else
0))
else
(if i.val < 3237 then
(if i.val < 3236 then
1
else
1)
else
(if i.val < 3238 then
1
else
(if i.val < 3239 then
1
else
1)))))))))))
else
(if i.val < 3780 then
(if i.val < 3510 then
(if i.val < 3375 then
(if i.val < 3307 then
(if i.val < 3273 then
(if i.val < 3256 then
(if i.val < 3248 then
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
0
else
1)
else
(if i.val < 3243 then
0
else
1))
else
(if i.val < 3246 then
(if i.val < 3245 then
0
else
1)
else
(if i.val < 3247 then
0
else
1)))
else
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
1
else
1)
else
(if i.val < 3251 then
1
else
1))
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
1))))
else
(if i.val < 3264 then
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
1
else
0)
else
(if i.val < 3259 then
1
else
0))
else
(if i.val < 3262 then
(if i.val < 3261 then
1
else
0)
else
(if i.val < 3263 then
0
else
0)))
else
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
1
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
0
else
1)
else
(if i.val < 3271 then
0
else
(if i.val < 3272 then
1
else
0))))))
else
(if i.val < 3290 then
(if i.val < 3281 then
(if i.val < 3277 then
(if i.val < 3275 then
(if i.val < 3274 then
1
else
1)
else
(if i.val < 3276 then
1
else
0))
else
(if i.val < 3279 then
(if i.val < 3278 then
1
else
0)
else
(if i.val < 3280 then
1
else
1)))
else
(if i.val < 3285 then
(if i.val < 3283 then
(if i.val < 3282 then
1
else
0)
else
(if i.val < 3284 then
1
else
1))
else
(if i.val < 3287 then
(if i.val < 3286 then
1
else
0)
else
(if i.val < 3288 then
0
else
(if i.val < 3289 then
1
else
0)))))
else
(if i.val < 3298 then
(if i.val < 3294 then
(if i.val < 3292 then
(if i.val < 3291 then
1
else
0)
else
(if i.val < 3293 then
1
else
0))
else
(if i.val < 3296 then
(if i.val < 3295 then
1
else
0)
else
(if i.val < 3297 then
1
else
0)))
else
(if i.val < 3302 then
(if i.val < 3300 then
(if i.val < 3299 then
1
else
0)
else
(if i.val < 3301 then
1
else
0))
else
(if i.val < 3304 then
(if i.val < 3303 then
1
else
0)
else
(if i.val < 3305 then
1
else
(if i.val < 3306 then
0
else
1)))))))
else
(if i.val < 3341 then
(if i.val < 3324 then
(if i.val < 3315 then
(if i.val < 3311 then
(if i.val < 3309 then
(if i.val < 3308 then
0
else
1)
else
(if i.val < 3310 then
0
else
1))
else
(if i.val < 3313 then
(if i.val < 3312 then
1
else
0)
else
(if i.val < 3314 then
1
else
1)))
else
(if i.val < 3319 then
(if i.val < 3317 then
(if i.val < 3316 then
0
else
0)
else
(if i.val < 3318 then
1
else
0))
else
(if i.val < 3321 then
(if i.val < 3320 then
0
else
1)
else
(if i.val < 3322 then
1
else
(if i.val < 3323 then
1
else
0)))))
else
(if i.val < 3332 then
(if i.val < 3328 then
(if i.val < 3326 then
(if i.val < 3325 then
1
else
1)
else
(if i.val < 3327 then
0
else
1))
else
(if i.val < 3330 then
(if i.val < 3329 then
0
else
1)
else
(if i.val < 3331 then
1
else
1)))
else
(if i.val < 3336 then
(if i.val < 3334 then
(if i.val < 3333 then
1
else
1)
else
(if i.val < 3335 then
0
else
1))
else
(if i.val < 3338 then
(if i.val < 3337 then
1
else
1)
else
(if i.val < 3339 then
0
else
(if i.val < 3340 then
1
else
1))))))
else
(if i.val < 3358 then
(if i.val < 3349 then
(if i.val < 3345 then
(if i.val < 3343 then
(if i.val < 3342 then
0
else
0)
else
(if i.val < 3344 then
0
else
1))
else
(if i.val < 3347 then
(if i.val < 3346 then
0
else
0)
else
(if i.val < 3348 then
1
else
1)))
else
(if i.val < 3353 then
(if i.val < 3351 then
(if i.val < 3350 then
0
else
1)
else
(if i.val < 3352 then
0
else
0))
else
(if i.val < 3355 then
(if i.val < 3354 then
1
else
1)
else
(if i.val < 3356 then
0
else
(if i.val < 3357 then
1
else
1)))))
else
(if i.val < 3366 then
(if i.val < 3362 then
(if i.val < 3360 then
(if i.val < 3359 then
0
else
1)
else
(if i.val < 3361 then
0
else
1))
else
(if i.val < 3364 then
(if i.val < 3363 then
0
else
1)
else
(if i.val < 3365 then
0
else
1)))
else
(if i.val < 3370 then
(if i.val < 3368 then
(if i.val < 3367 then
1
else
1)
else
(if i.val < 3369 then
0
else
1))
else
(if i.val < 3372 then
(if i.val < 3371 then
1
else
1)
else
(if i.val < 3373 then
1
else
(if i.val < 3374 then
1
else
0))))))))
else
(if i.val < 3442 then
(if i.val < 3408 then
(if i.val < 3391 then
(if i.val < 3383 then
(if i.val < 3379 then
(if i.val < 3377 then
(if i.val < 3376 then
1
else
0)
else
(if i.val < 3378 then
0
else
1))
else
(if i.val < 3381 then
(if i.val < 3380 then
1
else
1)
else
(if i.val < 3382 then
0
else
1)))
else
(if i.val < 3387 then
(if i.val < 3385 then
(if i.val < 3384 then
0
else
1)
else
(if i.val < 3386 then
0
else
0))
else
(if i.val < 3389 then
(if i.val < 3388 then
1
else
1)
else
(if i.val < 3390 then
0
else
0))))
else
(if i.val < 3399 then
(if i.val < 3395 then
(if i.val < 3393 then
(if i.val < 3392 then
0
else
1)
else
(if i.val < 3394 then
0
else
1))
else
(if i.val < 3397 then
(if i.val < 3396 then
0
else
1)
else
(if i.val < 3398 then
1
else
1)))
else
(if i.val < 3403 then
(if i.val < 3401 then
(if i.val < 3400 then
1
else
0)
else
(if i.val < 3402 then
1
else
1))
else
(if i.val < 3405 then
(if i.val < 3404 then
1
else
1)
else
(if i.val < 3406 then
0
else
(if i.val < 3407 then
1
else
1))))))
else
(if i.val < 3425 then
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
1
else
0)
else
(if i.val < 3411 then
1
else
1))
else
(if i.val < 3414 then
(if i.val < 3413 then
0
else
1)
else
(if i.val < 3415 then
0
else
1)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
1
else
0)
else
(if i.val < 3419 then
1
else
0))
else
(if i.val < 3422 then
(if i.val < 3421 then
1
else
0)
else
(if i.val < 3423 then
1
else
(if i.val < 3424 then
0
else
0)))))
else
(if i.val < 3433 then
(if i.val < 3429 then
(if i.val < 3427 then
(if i.val < 3426 then
0
else
1)
else
(if i.val < 3428 then
1
else
0))
else
(if i.val < 3431 then
(if i.val < 3430 then
1
else
1)
else
(if i.val < 3432 then
1
else
0)))
else
(if i.val < 3437 then
(if i.val < 3435 then
(if i.val < 3434 then
1
else
0)
else
(if i.val < 3436 then
1
else
1))
else
(if i.val < 3439 then
(if i.val < 3438 then
1
else
1)
else
(if i.val < 3440 then
0
else
(if i.val < 3441 then
1
else
0)))))))
else
(if i.val < 3476 then
(if i.val < 3459 then
(if i.val < 3450 then
(if i.val < 3446 then
(if i.val < 3444 then
(if i.val < 3443 then
0
else
1)
else
(if i.val < 3445 then
1
else
1))
else
(if i.val < 3448 then
(if i.val < 3447 then
1
else
0)
else
(if i.val < 3449 then
0
else
1)))
else
(if i.val < 3454 then
(if i.val < 3452 then
(if i.val < 3451 then
0
else
1)
else
(if i.val < 3453 then
1
else
1))
else
(if i.val < 3456 then
(if i.val < 3455 then
0
else
1)
else
(if i.val < 3457 then
0
else
(if i.val < 3458 then
1
else
0)))))
else
(if i.val < 3467 then
(if i.val < 3463 then
(if i.val < 3461 then
(if i.val < 3460 then
1
else
1)
else
(if i.val < 3462 then
1
else
0))
else
(if i.val < 3465 then
(if i.val < 3464 then
0
else
1)
else
(if i.val < 3466 then
0
else
1)))
else
(if i.val < 3471 then
(if i.val < 3469 then
(if i.val < 3468 then
0
else
1)
else
(if i.val < 3470 then
0
else
0))
else
(if i.val < 3473 then
(if i.val < 3472 then
1
else
1)
else
(if i.val < 3474 then
0
else
(if i.val < 3475 then
1
else
1))))))
else
(if i.val < 3493 then
(if i.val < 3484 then
(if i.val < 3480 then
(if i.val < 3478 then
(if i.val < 3477 then
1
else
0)
else
(if i.val < 3479 then
1
else
1))
else
(if i.val < 3482 then
(if i.val < 3481 then
1
else
1)
else
(if i.val < 3483 then
0
else
1)))
else
(if i.val < 3488 then
(if i.val < 3486 then
(if i.val < 3485 then
1
else
0)
else
(if i.val < 3487 then
1
else
0))
else
(if i.val < 3490 then
(if i.val < 3489 then
0
else
1)
else
(if i.val < 3491 then
1
else
(if i.val < 3492 then
0
else
0)))))
else
(if i.val < 3501 then
(if i.val < 3497 then
(if i.val < 3495 then
(if i.val < 3494 then
1
else
1)
else
(if i.val < 3496 then
1
else
0))
else
(if i.val < 3499 then
(if i.val < 3498 then
0
else
0)
else
(if i.val < 3500 then
1
else
0)))
else
(if i.val < 3505 then
(if i.val < 3503 then
(if i.val < 3502 then
1
else
1)
else
(if i.val < 3504 then
1
else
0))
else
(if i.val < 3507 then
(if i.val < 3506 then
1
else
0)
else
(if i.val < 3508 then
1
else
(if i.val < 3509 then
0
else
1)))))))))
else
(if i.val < 3645 then
(if i.val < 3577 then
(if i.val < 3543 then
(if i.val < 3526 then
(if i.val < 3518 then
(if i.val < 3514 then
(if i.val < 3512 then
(if i.val < 3511 then
1
else
0)
else
(if i.val < 3513 then
0
else
1))
else
(if i.val < 3516 then
(if i.val < 3515 then
1
else
1)
else
(if i.val < 3517 then
1
else
0)))
else
(if i.val < 3522 then
(if i.val < 3520 then
(if i.val < 3519 then
1
else
1)
else
(if i.val < 3521 then
0
else
1))
else
(if i.val < 3524 then
(if i.val < 3523 then
0
else
1)
else
(if i.val < 3525 then
0
else
0))))
else
(if i.val < 3534 then
(if i.val < 3530 then
(if i.val < 3528 then
(if i.val < 3527 then
1
else
1)
else
(if i.val < 3529 then
0
else
1))
else
(if i.val < 3532 then
(if i.val < 3531 then
0
else
0)
else
(if i.val < 3533 then
1
else
0)))
else
(if i.val < 3538 then
(if i.val < 3536 then
(if i.val < 3535 then
1
else
0)
else
(if i.val < 3537 then
0
else
0))
else
(if i.val < 3540 then
(if i.val < 3539 then
1
else
0)
else
(if i.val < 3541 then
1
else
(if i.val < 3542 then
1
else
0))))))
else
(if i.val < 3560 then
(if i.val < 3551 then
(if i.val < 3547 then
(if i.val < 3545 then
(if i.val < 3544 then
0
else
1)
else
(if i.val < 3546 then
0
else
1))
else
(if i.val < 3549 then
(if i.val < 3548 then
1
else
1)
else
(if i.val < 3550 then
0
else
0)))
else
(if i.val < 3555 then
(if i.val < 3553 then
(if i.val < 3552 then
1
else
0)
else
(if i.val < 3554 then
1
else
0))
else
(if i.val < 3557 then
(if i.val < 3556 then
0
else
1)
else
(if i.val < 3558 then
1
else
(if i.val < 3559 then
1
else
1)))))
else
(if i.val < 3568 then
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
0
else
0)
else
(if i.val < 3563 then
1
else
1))
else
(if i.val < 3566 then
(if i.val < 3565 then
1
else
1)
else
(if i.val < 3567 then
1
else
0)))
else
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
1
else
1)
else
(if i.val < 3571 then
0
else
1))
else
(if i.val < 3574 then
(if i.val < 3573 then
1
else
1)
else
(if i.val < 3575 then
1
else
(if i.val < 3576 then
1
else
1)))))))
else
(if i.val < 3611 then
(if i.val < 3594 then
(if i.val < 3585 then
(if i.val < 3581 then
(if i.val < 3579 then
(if i.val < 3578 then
0
else
0)
else
(if i.val < 3580 then
1
else
1))
else
(if i.val < 3583 then
(if i.val < 3582 then
0
else
1)
else
(if i.val < 3584 then
0
else
0)))
else
(if i.val < 3589 then
(if i.val < 3587 then
(if i.val < 3586 then
1
else
1)
else
(if i.val < 3588 then
0
else
1))
else
(if i.val < 3591 then
(if i.val < 3590 then
1
else
0)
else
(if i.val < 3592 then
1
else
(if i.val < 3593 then
1
else
0)))))
else
(if i.val < 3602 then
(if i.val < 3598 then
(if i.val < 3596 then
(if i.val < 3595 then
0
else
1)
else
(if i.val < 3597 then
0
else
0))
else
(if i.val < 3600 then
(if i.val < 3599 then
0
else
1)
else
(if i.val < 3601 then
1
else
1)))
else
(if i.val < 3606 then
(if i.val < 3604 then
(if i.val < 3603 then
1
else
0)
else
(if i.val < 3605 then
1
else
0))
else
(if i.val < 3608 then
(if i.val < 3607 then
1
else
1)
else
(if i.val < 3609 then
1
else
(if i.val < 3610 then
0
else
1))))))
else
(if i.val < 3628 then
(if i.val < 3619 then
(if i.val < 3615 then
(if i.val < 3613 then
(if i.val < 3612 then
0
else
1)
else
(if i.val < 3614 then
0
else
0))
else
(if i.val < 3617 then
(if i.val < 3616 then
1
else
1)
else
(if i.val < 3618 then
0
else
1)))
else
(if i.val < 3623 then
(if i.val < 3621 then
(if i.val < 3620 then
1
else
0)
else
(if i.val < 3622 then
1
else
1))
else
(if i.val < 3625 then
(if i.val < 3624 then
1
else
1)
else
(if i.val < 3626 then
1
else
(if i.val < 3627 then
1
else
1)))))
else
(if i.val < 3636 then
(if i.val < 3632 then
(if i.val < 3630 then
(if i.val < 3629 then
1
else
1)
else
(if i.val < 3631 then
1
else
1))
else
(if i.val < 3634 then
(if i.val < 3633 then
0
else
1)
else
(if i.val < 3635 then
0
else
0)))
else
(if i.val < 3640 then
(if i.val < 3638 then
(if i.val < 3637 then
0
else
1)
else
(if i.val < 3639 then
1
else
0))
else
(if i.val < 3642 then
(if i.val < 3641 then
1
else
0)
else
(if i.val < 3643 then
1
else
(if i.val < 3644 then
0
else
0))))))))
else
(if i.val < 3712 then
(if i.val < 3678 then
(if i.val < 3661 then
(if i.val < 3653 then
(if i.val < 3649 then
(if i.val < 3647 then
(if i.val < 3646 then
1
else
0)
else
(if i.val < 3648 then
1
else
1))
else
(if i.val < 3651 then
(if i.val < 3650 then
0
else
1)
else
(if i.val < 3652 then
0
else
1)))
else
(if i.val < 3657 then
(if i.val < 3655 then
(if i.val < 3654 then
0
else
1)
else
(if i.val < 3656 then
1
else
1))
else
(if i.val < 3659 then
(if i.val < 3658 then
0
else
0)
else
(if i.val < 3660 then
0
else
1))))
else
(if i.val < 3669 then
(if i.val < 3665 then
(if i.val < 3663 then
(if i.val < 3662 then
0
else
1)
else
(if i.val < 3664 then
0
else
1))
else
(if i.val < 3667 then
(if i.val < 3666 then
1
else
0)
else
(if i.val < 3668 then
1
else
1)))
else
(if i.val < 3673 then
(if i.val < 3671 then
(if i.val < 3670 then
1
else
1)
else
(if i.val < 3672 then
0
else
1))
else
(if i.val < 3675 then
(if i.val < 3674 then
1
else
1)
else
(if i.val < 3676 then
1
else
(if i.val < 3677 then
0
else
1))))))
else
(if i.val < 3695 then
(if i.val < 3686 then
(if i.val < 3682 then
(if i.val < 3680 then
(if i.val < 3679 then
1
else
0)
else
(if i.val < 3681 then
1
else
1))
else
(if i.val < 3684 then
(if i.val < 3683 then
0
else
0)
else
(if i.val < 3685 then
1
else
1)))
else
(if i.val < 3690 then
(if i.val < 3688 then
(if i.val < 3687 then
0
else
1)
else
(if i.val < 3689 then
1
else
1))
else
(if i.val < 3692 then
(if i.val < 3691 then
0
else
1)
else
(if i.val < 3693 then
1
else
(if i.val < 3694 then
1
else
0)))))
else
(if i.val < 3703 then
(if i.val < 3699 then
(if i.val < 3697 then
(if i.val < 3696 then
1
else
0)
else
(if i.val < 3698 then
1
else
1))
else
(if i.val < 3701 then
(if i.val < 3700 then
0
else
0)
else
(if i.val < 3702 then
1
else
1)))
else
(if i.val < 3707 then
(if i.val < 3705 then
(if i.val < 3704 then
1
else
0)
else
(if i.val < 3706 then
1
else
1))
else
(if i.val < 3709 then
(if i.val < 3708 then
0
else
1)
else
(if i.val < 3710 then
0
else
(if i.val < 3711 then
0
else
0)))))))
else
(if i.val < 3746 then
(if i.val < 3729 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
1
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
1)
else
(if i.val < 3719 then
1
else
1)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
1
else
0)
else
(if i.val < 3723 then
1
else
1))
else
(if i.val < 3726 then
(if i.val < 3725 then
1
else
1)
else
(if i.val < 3727 then
1
else
(if i.val < 3728 then
1
else
0)))))
else
(if i.val < 3737 then
(if i.val < 3733 then
(if i.val < 3731 then
(if i.val < 3730 then
0
else
1)
else
(if i.val < 3732 then
0
else
1))
else
(if i.val < 3735 then
(if i.val < 3734 then
0
else
1)
else
(if i.val < 3736 then
1
else
1)))
else
(if i.val < 3741 then
(if i.val < 3739 then
(if i.val < 3738 then
1
else
0)
else
(if i.val < 3740 then
1
else
0))
else
(if i.val < 3743 then
(if i.val < 3742 then
1
else
0)
else
(if i.val < 3744 then
1
else
(if i.val < 3745 then
1
else
1))))))
else
(if i.val < 3763 then
(if i.val < 3754 then
(if i.val < 3750 then
(if i.val < 3748 then
(if i.val < 3747 then
1
else
1)
else
(if i.val < 3749 then
1
else
0))
else
(if i.val < 3752 then
(if i.val < 3751 then
1
else
0)
else
(if i.val < 3753 then
1
else
1)))
else
(if i.val < 3758 then
(if i.val < 3756 then
(if i.val < 3755 then
1
else
0)
else
(if i.val < 3757 then
1
else
1))
else
(if i.val < 3760 then
(if i.val < 3759 then
1
else
0)
else
(if i.val < 3761 then
1
else
(if i.val < 3762 then
0
else
1)))))
else
(if i.val < 3771 then
(if i.val < 3767 then
(if i.val < 3765 then
(if i.val < 3764 then
0
else
1)
else
(if i.val < 3766 then
1
else
0))
else
(if i.val < 3769 then
(if i.val < 3768 then
1
else
1)
else
(if i.val < 3770 then
0
else
1)))
else
(if i.val < 3775 then
(if i.val < 3773 then
(if i.val < 3772 then
1
else
0)
else
(if i.val < 3774 then
1
else
1))
else
(if i.val < 3777 then
(if i.val < 3776 then
0
else
0)
else
(if i.val < 3778 then
0
else
(if i.val < 3779 then
1
else
1))))))))))
else
(if i.val < 4050 then
(if i.val < 3915 then
(if i.val < 3847 then
(if i.val < 3813 then
(if i.val < 3796 then
(if i.val < 3788 then
(if i.val < 3784 then
(if i.val < 3782 then
(if i.val < 3781 then
0
else
0)
else
(if i.val < 3783 then
1
else
1))
else
(if i.val < 3786 then
(if i.val < 3785 then
0
else
1)
else
(if i.val < 3787 then
0
else
0)))
else
(if i.val < 3792 then
(if i.val < 3790 then
(if i.val < 3789 then
1
else
1)
else
(if i.val < 3791 then
1
else
1))
else
(if i.val < 3794 then
(if i.val < 3793 then
1
else
1)
else
(if i.val < 3795 then
1
else
0))))
else
(if i.val < 3804 then
(if i.val < 3800 then
(if i.val < 3798 then
(if i.val < 3797 then
1
else
1)
else
(if i.val < 3799 then
1
else
0))
else
(if i.val < 3802 then
(if i.val < 3801 then
0
else
1)
else
(if i.val < 3803 then
1
else
0)))
else
(if i.val < 3808 then
(if i.val < 3806 then
(if i.val < 3805 then
1
else
1)
else
(if i.val < 3807 then
1
else
0))
else
(if i.val < 3810 then
(if i.val < 3809 then
1
else
0)
else
(if i.val < 3811 then
0
else
(if i.val < 3812 then
0
else
1))))))
else
(if i.val < 3830 then
(if i.val < 3821 then
(if i.val < 3817 then
(if i.val < 3815 then
(if i.val < 3814 then
1
else
1)
else
(if i.val < 3816 then
1
else
0))
else
(if i.val < 3819 then
(if i.val < 3818 then
0
else
1)
else
(if i.val < 3820 then
1
else
0)))
else
(if i.val < 3825 then
(if i.val < 3823 then
(if i.val < 3822 then
1
else
1)
else
(if i.val < 3824 then
1
else
1))
else
(if i.val < 3827 then
(if i.val < 3826 then
0
else
1)
else
(if i.val < 3828 then
0
else
(if i.val < 3829 then
1
else
0)))))
else
(if i.val < 3838 then
(if i.val < 3834 then
(if i.val < 3832 then
(if i.val < 3831 then
1
else
1)
else
(if i.val < 3833 then
1
else
1))
else
(if i.val < 3836 then
(if i.val < 3835 then
0
else
1)
else
(if i.val < 3837 then
1
else
0)))
else
(if i.val < 3842 then
(if i.val < 3840 then
(if i.val < 3839 then
1
else
1)
else
(if i.val < 3841 then
0
else
1))
else
(if i.val < 3844 then
(if i.val < 3843 then
0
else
1)
else
(if i.val < 3845 then
0
else
(if i.val < 3846 then
1
else
0)))))))
else
(if i.val < 3881 then
(if i.val < 3864 then
(if i.val < 3855 then
(if i.val < 3851 then
(if i.val < 3849 then
(if i.val < 3848 then
0
else
1)
else
(if i.val < 3850 then
0
else
1))
else
(if i.val < 3853 then
(if i.val < 3852 then
0
else
1)
else
(if i.val < 3854 then
1
else
1)))
else
(if i.val < 3859 then
(if i.val < 3857 then
(if i.val < 3856 then
0
else
1)
else
(if i.val < 3858 then
1
else
1))
else
(if i.val < 3861 then
(if i.val < 3860 then
0
else
0)
else
(if i.val < 3862 then
1
else
(if i.val < 3863 then
0
else
1)))))
else
(if i.val < 3872 then
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
0
else
1)
else
(if i.val < 3867 then
0
else
1))
else
(if i.val < 3870 then
(if i.val < 3869 then
1
else
1)
else
(if i.val < 3871 then
1
else
1)))
else
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
1
else
1)
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
1)
else
(if i.val < 3879 then
1
else
(if i.val < 3880 then
1
else
1))))))
else
(if i.val < 3898 then
(if i.val < 3889 then
(if i.val < 3885 then
(if i.val < 3883 then
(if i.val < 3882 then
0
else
1)
else
(if i.val < 3884 then
1
else
0))
else
(if i.val < 3887 then
(if i.val < 3886 then
0
else
0)
else
(if i.val < 3888 then
1
else
1)))
else
(if i.val < 3893 then
(if i.val < 3891 then
(if i.val < 3890 then
0
else
1)
else
(if i.val < 3892 then
1
else
0))
else
(if i.val < 3895 then
(if i.val < 3894 then
1
else
1)
else
(if i.val < 3896 then
1
else
(if i.val < 3897 then
0
else
1)))))
else
(if i.val < 3906 then
(if i.val < 3902 then
(if i.val < 3900 then
(if i.val < 3899 then
1
else
1)
else
(if i.val < 3901 then
1
else
0))
else
(if i.val < 3904 then
(if i.val < 3903 then
0
else
0)
else
(if i.val < 3905 then
1
else
1)))
else
(if i.val < 3910 then
(if i.val < 3908 then
(if i.val < 3907 then
1
else
1)
else
(if i.val < 3909 then
1
else
0))
else
(if i.val < 3912 then
(if i.val < 3911 then
1
else
0)
else
(if i.val < 3913 then
1
else
(if i.val < 3914 then
0
else
0))))))))
else
(if i.val < 3982 then
(if i.val < 3948 then
(if i.val < 3931 then
(if i.val < 3923 then
(if i.val < 3919 then
(if i.val < 3917 then
(if i.val < 3916 then
1
else
0)
else
(if i.val < 3918 then
0
else
1))
else
(if i.val < 3921 then
(if i.val < 3920 then
0
else
1)
else
(if i.val < 3922 then
1
else
1)))
else
(if i.val < 3927 then
(if i.val < 3925 then
(if i.val < 3924 then
1
else
1)
else
(if i.val < 3926 then
1
else
1))
else
(if i.val < 3929 then
(if i.val < 3928 then
0
else
1)
else
(if i.val < 3930 then
0
else
1))))
else
(if i.val < 3939 then
(if i.val < 3935 then
(if i.val < 3933 then
(if i.val < 3932 then
1
else
0)
else
(if i.val < 3934 then
1
else
0))
else
(if i.val < 3937 then
(if i.val < 3936 then
1
else
0)
else
(if i.val < 3938 then
1
else
0)))
else
(if i.val < 3943 then
(if i.val < 3941 then
(if i.val < 3940 then
1
else
1)
else
(if i.val < 3942 then
1
else
1))
else
(if i.val < 3945 then
(if i.val < 3944 then
1
else
0)
else
(if i.val < 3946 then
0
else
(if i.val < 3947 then
1
else
1))))))
else
(if i.val < 3965 then
(if i.val < 3956 then
(if i.val < 3952 then
(if i.val < 3950 then
(if i.val < 3949 then
1
else
1)
else
(if i.val < 3951 then
1
else
0))
else
(if i.val < 3954 then
(if i.val < 3953 then
1
else
0)
else
(if i.val < 3955 then
0
else
0)))
else
(if i.val < 3960 then
(if i.val < 3958 then
(if i.val < 3957 then
1
else
0)
else
(if i.val < 3959 then
0
else
1))
else
(if i.val < 3962 then
(if i.val < 3961 then
1
else
1)
else
(if i.val < 3963 then
1
else
(if i.val < 3964 then
1
else
1)))))
else
(if i.val < 3973 then
(if i.val < 3969 then
(if i.val < 3967 then
(if i.val < 3966 then
0
else
1)
else
(if i.val < 3968 then
1
else
1))
else
(if i.val < 3971 then
(if i.val < 3970 then
1
else
0)
else
(if i.val < 3972 then
1
else
0)))
else
(if i.val < 3977 then
(if i.val < 3975 then
(if i.val < 3974 then
1
else
0)
else
(if i.val < 3976 then
0
else
1))
else
(if i.val < 3979 then
(if i.val < 3978 then
1
else
0)
else
(if i.val < 3980 then
1
else
(if i.val < 3981 then
0
else
0)))))))
else
(if i.val < 4016 then
(if i.val < 3999 then
(if i.val < 3990 then
(if i.val < 3986 then
(if i.val < 3984 then
(if i.val < 3983 then
1
else
0)
else
(if i.val < 3985 then
1
else
0))
else
(if i.val < 3988 then
(if i.val < 3987 then
0
else
1)
else
(if i.val < 3989 then
0
else
0)))
else
(if i.val < 3994 then
(if i.val < 3992 then
(if i.val < 3991 then
1
else
0)
else
(if i.val < 3993 then
0
else
1))
else
(if i.val < 3996 then
(if i.val < 3995 then
0
else
0)
else
(if i.val < 3997 then
1
else
(if i.val < 3998 then
1
else
1)))))
else
(if i.val < 4007 then
(if i.val < 4003 then
(if i.val < 4001 then
(if i.val < 4000 then
1
else
1)
else
(if i.val < 4002 then
0
else
1))
else
(if i.val < 4005 then
(if i.val < 4004 then
1
else
0)
else
(if i.val < 4006 then
0
else
1)))
else
(if i.val < 4011 then
(if i.val < 4009 then
(if i.val < 4008 then
1
else
0)
else
(if i.val < 4010 then
1
else
1))
else
(if i.val < 4013 then
(if i.val < 4012 then
1
else
0)
else
(if i.val < 4014 then
1
else
(if i.val < 4015 then
1
else
0))))))
else
(if i.val < 4033 then
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
1
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
1
else
1)
else
(if i.val < 4023 then
0
else
1)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
1
else
1)
else
(if i.val < 4027 then
1
else
1))
else
(if i.val < 4030 then
(if i.val < 4029 then
0
else
1)
else
(if i.val < 4031 then
0
else
(if i.val < 4032 then
0
else
1)))))
else
(if i.val < 4041 then
(if i.val < 4037 then
(if i.val < 4035 then
(if i.val < 4034 then
0
else
0)
else
(if i.val < 4036 then
1
else
1))
else
(if i.val < 4039 then
(if i.val < 4038 then
0
else
0)
else
(if i.val < 4040 then
1
else
1)))
else
(if i.val < 4045 then
(if i.val < 4043 then
(if i.val < 4042 then
0
else
1)
else
(if i.val < 4044 then
1
else
1))
else
(if i.val < 4047 then
(if i.val < 4046 then
1
else
0)
else
(if i.val < 4048 then
1
else
(if i.val < 4049 then
0
else
1)))))))))
else
(if i.val < 4185 then
(if i.val < 4117 then
(if i.val < 4083 then
(if i.val < 4066 then
(if i.val < 4058 then
(if i.val < 4054 then
(if i.val < 4052 then
(if i.val < 4051 then
0
else
1)
else
(if i.val < 4053 then
1
else
1))
else
(if i.val < 4056 then
(if i.val < 4055 then
1
else
0)
else
(if i.val < 4057 then
1
else
0)))
else
(if i.val < 4062 then
(if i.val < 4060 then
(if i.val < 4059 then
0
else
1)
else
(if i.val < 4061 then
1
else
0))
else
(if i.val < 4064 then
(if i.val < 4063 then
0
else
0)
else
(if i.val < 4065 then
1
else
1))))
else
(if i.val < 4074 then
(if i.val < 4070 then
(if i.val < 4068 then
(if i.val < 4067 then
1
else
1)
else
(if i.val < 4069 then
1
else
0))
else
(if i.val < 4072 then
(if i.val < 4071 then
1
else
1)
else
(if i.val < 4073 then
0
else
1)))
else
(if i.val < 4078 then
(if i.val < 4076 then
(if i.val < 4075 then
1
else
1)
else
(if i.val < 4077 then
1
else
1))
else
(if i.val < 4080 then
(if i.val < 4079 then
0
else
1)
else
(if i.val < 4081 then
1
else
(if i.val < 4082 then
1
else
1))))))
else
(if i.val < 4100 then
(if i.val < 4091 then
(if i.val < 4087 then
(if i.val < 4085 then
(if i.val < 4084 then
1
else
0)
else
(if i.val < 4086 then
1
else
1))
else
(if i.val < 4089 then
(if i.val < 4088 then
0
else
1)
else
(if i.val < 4090 then
0
else
0)))
else
(if i.val < 4095 then
(if i.val < 4093 then
(if i.val < 4092 then
1
else
0)
else
(if i.val < 4094 then
0
else
1))
else
(if i.val < 4097 then
(if i.val < 4096 then
1
else
0)
else
(if i.val < 4098 then
0
else
(if i.val < 4099 then
1
else
1)))))
else
(if i.val < 4108 then
(if i.val < 4104 then
(if i.val < 4102 then
(if i.val < 4101 then
0
else
1)
else
(if i.val < 4103 then
1
else
1))
else
(if i.val < 4106 then
(if i.val < 4105 then
1
else
1)
else
(if i.val < 4107 then
1
else
0)))
else
(if i.val < 4112 then
(if i.val < 4110 then
(if i.val < 4109 then
0
else
0)
else
(if i.val < 4111 then
1
else
0))
else
(if i.val < 4114 then
(if i.val < 4113 then
1
else
1)
else
(if i.val < 4115 then
1
else
(if i.val < 4116 then
1
else
0)))))))
else
(if i.val < 4151 then
(if i.val < 4134 then
(if i.val < 4125 then
(if i.val < 4121 then
(if i.val < 4119 then
(if i.val < 4118 then
0
else
1)
else
(if i.val < 4120 then
1
else
0))
else
(if i.val < 4123 then
(if i.val < 4122 then
1
else
1)
else
(if i.val < 4124 then
0
else
1)))
else
(if i.val < 4129 then
(if i.val < 4127 then
(if i.val < 4126 then
1
else
1)
else
(if i.val < 4128 then
1
else
0))
else
(if i.val < 4131 then
(if i.val < 4130 then
1
else
1)
else
(if i.val < 4132 then
1
else
(if i.val < 4133 then
1
else
1)))))
else
(if i.val < 4142 then
(if i.val < 4138 then
(if i.val < 4136 then
(if i.val < 4135 then
1
else
1)
else
(if i.val < 4137 then
1
else
1))
else
(if i.val < 4140 then
(if i.val < 4139 then
1
else
0)
else
(if i.val < 4141 then
1
else
1)))
else
(if i.val < 4146 then
(if i.val < 4144 then
(if i.val < 4143 then
0
else
1)
else
(if i.val < 4145 then
0
else
1))
else
(if i.val < 4148 then
(if i.val < 4147 then
1
else
1)
else
(if i.val < 4149 then
0
else
(if i.val < 4150 then
0
else
0))))))
else
(if i.val < 4168 then
(if i.val < 4159 then
(if i.val < 4155 then
(if i.val < 4153 then
(if i.val < 4152 then
1
else
1)
else
(if i.val < 4154 then
0
else
1))
else
(if i.val < 4157 then
(if i.val < 4156 then
0
else
0)
else
(if i.val < 4158 then
0
else
1)))
else
(if i.val < 4163 then
(if i.val < 4161 then
(if i.val < 4160 then
0
else
0)
else
(if i.val < 4162 then
0
else
1))
else
(if i.val < 4165 then
(if i.val < 4164 then
0
else
1)
else
(if i.val < 4166 then
0
else
(if i.val < 4167 then
1
else
0)))))
else
(if i.val < 4176 then
(if i.val < 4172 then
(if i.val < 4170 then
(if i.val < 4169 then
1
else
1)
else
(if i.val < 4171 then
1
else
0))
else
(if i.val < 4174 then
(if i.val < 4173 then
1
else
1)
else
(if i.val < 4175 then
1
else
1)))
else
(if i.val < 4180 then
(if i.val < 4178 then
(if i.val < 4177 then
0
else
1)
else
(if i.val < 4179 then
1
else
1))
else
(if i.val < 4182 then
(if i.val < 4181 then
0
else
1)
else
(if i.val < 4183 then
1
else
(if i.val < 4184 then
1
else
1))))))))
else
(if i.val < 4252 then
(if i.val < 4218 then
(if i.val < 4201 then
(if i.val < 4193 then
(if i.val < 4189 then
(if i.val < 4187 then
(if i.val < 4186 then
0
else
0)
else
(if i.val < 4188 then
0
else
0))
else
(if i.val < 4191 then
(if i.val < 4190 then
0
else
1)
else
(if i.val < 4192 then
0
else
1)))
else
(if i.val < 4197 then
(if i.val < 4195 then
(if i.val < 4194 then
0
else
1)
else
(if i.val < 4196 then
0
else
1))
else
(if i.val < 4199 then
(if i.val < 4198 then
1
else
1)
else
(if i.val < 4200 then
1
else
1))))
else
(if i.val < 4209 then
(if i.val < 4205 then
(if i.val < 4203 then
(if i.val < 4202 then
1
else
1)
else
(if i.val < 4204 then
1
else
0))
else
(if i.val < 4207 then
(if i.val < 4206 then
1
else
1)
else
(if i.val < 4208 then
1
else
1)))
else
(if i.val < 4213 then
(if i.val < 4211 then
(if i.val < 4210 then
0
else
1)
else
(if i.val < 4212 then
1
else
0))
else
(if i.val < 4215 then
(if i.val < 4214 then
0
else
0)
else
(if i.val < 4216 then
1
else
(if i.val < 4217 then
1
else
1))))))
else
(if i.val < 4235 then
(if i.val < 4226 then
(if i.val < 4222 then
(if i.val < 4220 then
(if i.val < 4219 then
1
else
1)
else
(if i.val < 4221 then
1
else
0))
else
(if i.val < 4224 then
(if i.val < 4223 then
0
else
1)
else
(if i.val < 4225 then
1
else
0)))
else
(if i.val < 4230 then
(if i.val < 4228 then
(if i.val < 4227 then
0
else
0)
else
(if i.val < 4229 then
1
else
1))
else
(if i.val < 4232 then
(if i.val < 4231 then
1
else
1)
else
(if i.val < 4233 then
0
else
(if i.val < 4234 then
1
else
0)))))
else
(if i.val < 4243 then
(if i.val < 4239 then
(if i.val < 4237 then
(if i.val < 4236 then
1
else
0)
else
(if i.val < 4238 then
1
else
0))
else
(if i.val < 4241 then
(if i.val < 4240 then
1
else
1)
else
(if i.val < 4242 then
1
else
0)))
else
(if i.val < 4247 then
(if i.val < 4245 then
(if i.val < 4244 then
1
else
1)
else
(if i.val < 4246 then
1
else
1))
else
(if i.val < 4249 then
(if i.val < 4248 then
1
else
1)
else
(if i.val < 4250 then
1
else
(if i.val < 4251 then
0
else
1)))))))
else
(if i.val < 4286 then
(if i.val < 4269 then
(if i.val < 4260 then
(if i.val < 4256 then
(if i.val < 4254 then
(if i.val < 4253 then
1
else
1)
else
(if i.val < 4255 then
0
else
1))
else
(if i.val < 4258 then
(if i.val < 4257 then
1
else
1)
else
(if i.val < 4259 then
0
else
0)))
else
(if i.val < 4264 then
(if i.val < 4262 then
(if i.val < 4261 then
1
else
1)
else
(if i.val < 4263 then
1
else
1))
else
(if i.val < 4266 then
(if i.val < 4265 then
1
else
1)
else
(if i.val < 4267 then
1
else
(if i.val < 4268 then
1
else
0)))))
else
(if i.val < 4277 then
(if i.val < 4273 then
(if i.val < 4271 then
(if i.val < 4270 then
0
else
1)
else
(if i.val < 4272 then
1
else
1))
else
(if i.val < 4275 then
(if i.val < 4274 then
1
else
1)
else
(if i.val < 4276 then
1
else
1)))
else
(if i.val < 4281 then
(if i.val < 4279 then
(if i.val < 4278 then
1
else
1)
else
(if i.val < 4280 then
0
else
0))
else
(if i.val < 4283 then
(if i.val < 4282 then
0
else
1)
else
(if i.val < 4284 then
1
else
(if i.val < 4285 then
1
else
1))))))
else
(if i.val < 4303 then
(if i.val < 4294 then
(if i.val < 4290 then
(if i.val < 4288 then
(if i.val < 4287 then
1
else
1)
else
(if i.val < 4289 then
1
else
0))
else
(if i.val < 4292 then
(if i.val < 4291 then
0
else
0)
else
(if i.val < 4293 then
1
else
1)))
else
(if i.val < 4298 then
(if i.val < 4296 then
(if i.val < 4295 then
1
else
1)
else
(if i.val < 4297 then
1
else
1))
else
(if i.val < 4300 then
(if i.val < 4299 then
1
else
1)
else
(if i.val < 4301 then
1
else
(if i.val < 4302 then
0
else
0)))))
else
(if i.val < 4311 then
(if i.val < 4307 then
(if i.val < 4305 then
(if i.val < 4304 then
1
else
0)
else
(if i.val < 4306 then
0
else
0))
else
(if i.val < 4309 then
(if i.val < 4308 then
0
else
1)
else
(if i.val < 4310 then
0
else
1)))
else
(if i.val < 4315 then
(if i.val < 4313 then
(if i.val < 4312 then
1
else
1)
else
(if i.val < 4314 then
1
else
0))
else
(if i.val < 4317 then
(if i.val < 4316 then
0
else
1)
else
(if i.val < 4318 then
1
else
(if i.val < 4319 then
1
else
1)))))))))))))


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row03_groupNext : Fin 4320 → Fin 2 → Fin 4320 :=
  fun i => (if i.val < 2160 then
(if i.val < 1080 then
(if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
![1, 2]
else
![3, 4])
else
(if i.val < 3 then
![5, 6]
else
![7, 8]))
else
(if i.val < 6 then
(if i.val < 5 then
![9, 10]
else
![11, 12])
else
(if i.val < 7 then
![13, 14]
else
![15, 16])))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
![17, 18]
else
![19, 20])
else
(if i.val < 11 then
![21, 22]
else
![23, 24]))
else
(if i.val < 14 then
(if i.val < 13 then
![25, 26]
else
![27, 28])
else
(if i.val < 15 then
![29, 30]
else
![31, 32]))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
![33, 34]
else
![35, 36])
else
(if i.val < 19 then
![37, 38]
else
![39, 40]))
else
(if i.val < 22 then
(if i.val < 21 then
![41, 42]
else
![43, 44])
else
(if i.val < 23 then
![45, 46]
else
![32, 47])))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
![48, 49]
else
![50, 51])
else
(if i.val < 27 then
![52, 53]
else
![54, 55]))
else
(if i.val < 30 then
(if i.val < 29 then
![56, 57]
else
![58, 59])
else
(if i.val < 31 then
![46, 60]
else
(if i.val < 32 then
![61, 62]
else
![63, 64]))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
![65, 66]
else
![67, 68])
else
(if i.val < 36 then
![69, 70]
else
![71, 72]))
else
(if i.val < 39 then
(if i.val < 38 then
![73, 74]
else
![75, 76])
else
(if i.val < 40 then
![62, 77]
else
![78, 79])))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
![80, 81]
else
![82, 83])
else
(if i.val < 44 then
![84, 85]
else
![86, 87]))
else
(if i.val < 47 then
(if i.val < 46 then
![88, 89]
else
![76, 90])
else
(if i.val < 48 then
![91, 92]
else
(if i.val < 49 then
![93, 94]
else
![95, 96])))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
![97, 98]
else
![99, 100])
else
(if i.val < 53 then
![101, 102]
else
![103, 104]))
else
(if i.val < 56 then
(if i.val < 55 then
![64, 105]
else
![106, 107])
else
(if i.val < 57 then
![108, 109]
else
![110, 111])))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
![112, 113]
else
![114, 115])
else
(if i.val < 61 then
![104, 116]
else
![117, 118]))
else
(if i.val < 64 then
(if i.val < 63 then
![119, 120]
else
![121, 122])
else
(if i.val < 65 then
![123, 124]
else
(if i.val < 66 then
![125, 126]
else
![127, 128])))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
![129, 130]
else
![131, 132])
else
(if i.val < 70 then
![118, 133]
else
![134, 135]))
else
(if i.val < 73 then
(if i.val < 72 then
![136, 137]
else
![138, 139])
else
(if i.val < 74 then
![140, 141]
else
![142, 143])))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
![144, 145]
else
![132, 146])
else
(if i.val < 78 then
![147, 148]
else
![149, 150]))
else
(if i.val < 81 then
(if i.val < 80 then
![151, 152]
else
![153, 154])
else
(if i.val < 82 then
![14, 155]
else
(if i.val < 83 then
![156, 157]
else
![158, 159])))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
![120, 160]
else
![161, 162])
else
(if i.val < 87 then
![163, 164]
else
![165, 166]))
else
(if i.val < 90 then
(if i.val < 89 then
![167, 168]
else
![169, 170])
else
(if i.val < 91 then
![159, 171]
else
![172, 173])))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
![174, 175]
else
![176, 144])
else
(if i.val < 95 then
![177, 178]
else
![179, 180]))
else
(if i.val < 98 then
(if i.val < 97 then
![181, 182]
else
![122, 183])
else
(if i.val < 99 then
![184, 185]
else
(if i.val < 100 then
![186, 187]
else
![188, 189]))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
![190, 191]
else
![192, 193])
else
(if i.val < 104 then
![194, 195]
else
![182, 196]))
else
(if i.val < 107 then
(if i.val < 106 then
![197, 198]
else
![199, 200])
else
(if i.val < 108 then
![201, 202]
else
![203, 204])))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
![205, 206]
else
![207, 208])
else
(if i.val < 112 then
![209, 210]
else
![124, 211]))
else
(if i.val < 115 then
(if i.val < 114 then
![212, 213]
else
![214, 215])
else
(if i.val < 116 then
![216, 217]
else
(if i.val < 117 then
![210, 218]
else
![0, 219])))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
![220, 221]
else
![222, 223])
else
(if i.val < 121 then
![224, 225]
else
![226, 227]))
else
(if i.val < 124 then
(if i.val < 123 then
![228, 229]
else
![230, 231])
else
(if i.val < 125 then
![232, 233]
else
![219, 234])))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
![235, 236]
else
![237, 238])
else
(if i.val < 129 then
![239, 240]
else
![241, 242]))
else
(if i.val < 132 then
(if i.val < 131 then
![243, 244]
else
![245, 246])
else
(if i.val < 133 then
![233, 247]
else
(if i.val < 134 then
![248, 249]
else
![250, 251]))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
![252, 253]
else
![254, 255])
else
(if i.val < 138 then
![22, 256]
else
![257, 258]))
else
(if i.val < 141 then
(if i.val < 140 then
![259, 260]
else
![221, 261])
else
(if i.val < 142 then
![262, 263]
else
![264, 265])))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
![266, 267]
else
![268, 269])
else
(if i.val < 146 then
![270, 271]
else
![260, 272]))
else
(if i.val < 149 then
(if i.val < 148 then
![273, 274]
else
![275, 276])
else
(if i.val < 150 then
![277, 245]
else
![278, 279]))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
![280, 281]
else
![282, 283])
else
(if i.val < 154 then
![223, 284]
else
![285, 286]))
else
(if i.val < 157 then
(if i.val < 156 then
![287, 288]
else
![289, 290])
else
(if i.val < 158 then
![291, 292]
else
![293, 294])))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
![283, 295]
else
![296, 297])
else
(if i.val < 162 then
![298, 299]
else
![300, 301]))
else
(if i.val < 165 then
(if i.val < 164 then
![302, 303]
else
![304, 305])
else
(if i.val < 166 then
![306, 307]
else
(if i.val < 167 then
![308, 309]
else
![225, 310]))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
![311, 312]
else
![313, 314])
else
(if i.val < 171 then
![315, 316]
else
![309, 317]))
else
(if i.val < 174 then
(if i.val < 173 then
![318, 319]
else
![320, 321])
else
(if i.val < 175 then
![322, 323]
else
![324, 325])))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
![227, 326]
else
![327, 328])
else
(if i.val < 179 then
![329, 330]
else
![331, 332]))
else
(if i.val < 182 then
(if i.val < 181 then
![333, 334]
else
![335, 336])
else
(if i.val < 183 then
![325, 337]
else
(if i.val < 184 then
![338, 339]
else
![340, 341])))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
![342, 343]
else
![344, 345])
else
(if i.val < 188 then
![30, 346]
else
![347, 348]))
else
(if i.val < 191 then
(if i.val < 190 then
![349, 350]
else
![229, 351])
else
(if i.val < 192 then
![352, 353]
else
![354, 355])))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
![356, 357]
else
![358, 359])
else
(if i.val < 196 then
![360, 361]
else
![350, 362]))
else
(if i.val < 199 then
(if i.val < 198 then
![363, 364]
else
![365, 366])
else
(if i.val < 200 then
![367, 335]
else
(if i.val < 201 then
![368, 369]
else
![370, 371])))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
![372, 373]
else
![231, 374])
else
(if i.val < 205 then
![375, 376]
else
![377, 378]))
else
(if i.val < 208 then
(if i.val < 207 then
![379, 380]
else
![381, 382])
else
(if i.val < 209 then
![383, 384]
else
![385, 386])))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
![373, 387]
else
![388, 389])
else
(if i.val < 213 then
![390, 391]
else
![392, 393]))
else
(if i.val < 216 then
(if i.val < 215 then
![394, 395]
else
![396, 397])
else
(if i.val < 217 then
![398, 399]
else
(if i.val < 218 then
![400, 401]
else
![401, 402])))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
![403, 404]
else
![405, 406])
else
(if i.val < 222 then
![407, 408]
else
![409, 410]))
else
(if i.val < 225 then
(if i.val < 224 then
![411, 412]
else
![413, 414])
else
(if i.val < 226 then
![415, 416]
else
![2, 417])))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
![418, 419]
else
![420, 421])
else
(if i.val < 230 then
![422, 423]
else
![424, 425]))
else
(if i.val < 233 then
(if i.val < 232 then
![426, 427]
else
![428, 429])
else
(if i.val < 234 then
![416, 430]
else
(if i.val < 235 then
![431, 432]
else
![433, 434]))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
![435, 436]
else
![437, 438])
else
(if i.val < 239 then
![38, 439]
else
![440, 441]))
else
(if i.val < 242 then
(if i.val < 241 then
![442, 443]
else
![404, 444])
else
(if i.val < 243 then
![445, 446]
else
![447, 448])))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
![449, 450]
else
![51, 451])
else
(if i.val < 247 then
![452, 453]
else
![443, 454]))
else
(if i.val < 250 then
(if i.val < 249 then
![455, 456]
else
![380, 457])
else
(if i.val < 251 then
![458, 428]
else
(if i.val < 252 then
![459, 460]
else
![461, 462])))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
![463, 464]
else
![406, 465])
else
(if i.val < 256 then
![466, 467]
else
![468, 469]))
else
(if i.val < 259 then
(if i.val < 258 then
![470, 471]
else
![472, 473])
else
(if i.val < 260 then
![474, 475]
else
![464, 476])))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
![477, 478]
else
![479, 480])
else
(if i.val < 264 then
![481, 482]
else
![483, 484]))
else
(if i.val < 267 then
(if i.val < 266 then
![485, 486]
else
![487, 488])
else
(if i.val < 268 then
![489, 490]
else
(if i.val < 269 then
![408, 491]
else
![492, 493])))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
![494, 495]
else
![496, 497])
else
(if i.val < 273 then
![490, 498]
else
![499, 500]))
else
(if i.val < 276 then
(if i.val < 275 then
![501, 502]
else
![503, 504])
else
(if i.val < 277 then
![505, 506]
else
![410, 507])))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
![508, 509]
else
![510, 511])
else
(if i.val < 281 then
![512, 513]
else
![514, 515]))
else
(if i.val < 284 then
(if i.val < 283 then
![516, 517]
else
![506, 518])
else
(if i.val < 285 then
![519, 520]
else
![521, 522]))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
![523, 524]
else
![525, 526])
else
(if i.val < 289 then
![527, 528]
else
![412, 529]))
else
(if i.val < 292 then
(if i.val < 291 then
![530, 531]
else
![532, 533])
else
(if i.val < 293 then
![534, 535]
else
![536, 537])))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
![206, 538]
else
![528, 539])
else
(if i.val < 297 then
![540, 541]
else
![542, 543]))
else
(if i.val < 300 then
(if i.val < 299 then
![544, 516]
else
![545, 546])
else
(if i.val < 301 then
![547, 548]
else
(if i.val < 302 then
![549, 550]
else
![414, 551]))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
![552, 553]
else
![554, 555])
else
(if i.val < 306 then
![556, 557]
else
![558, 559]))
else
(if i.val < 309 then
(if i.val < 308 then
![560, 561]
else
![562, 563])
else
(if i.val < 310 then
![550, 564]
else
![565, 566])))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
![567, 568]
else
![569, 570])
else
(if i.val < 314 then
![571, 572]
else
![573, 574]))
else
(if i.val < 317 then
(if i.val < 316 then
![575, 576]
else
![577, 578])
else
(if i.val < 318 then
![578, 579]
else
(if i.val < 319 then
![417, 580]
else
![581, 582])))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
![583, 584]
else
![551, 585])
else
(if i.val < 323 then
![586, 587]
else
![588, 589]))
else
(if i.val < 326 then
(if i.val < 325 then
![590, 591]
else
![430, 592])
else
(if i.val < 327 then
![593, 594]
else
![595, 596])))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
![53, 597]
else
![598, 248])
else
(if i.val < 331 then
![599, 600]
else
![419, 601]))
else
(if i.val < 334 then
(if i.val < 333 then
![602, 603]
else
![604, 605])
else
(if i.val < 335 then
![606, 607]
else
(if i.val < 336 then
![608, 609]
else
![610, 611])))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
![600, 612]
else
![613, 614])
else
(if i.val < 340 then
![615, 616]
else
![617, 590]))
else
(if i.val < 343 then
(if i.val < 342 then
![618, 619]
else
![620, 621])
else
(if i.val < 344 then
![622, 623]
else
![421, 624])))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
![625, 626]
else
![627, 628])
else
(if i.val < 348 then
![629, 630]
else
![511, 262]))
else
(if i.val < 351 then
(if i.val < 350 then
![631, 632]
else
![623, 633])
else
(if i.val < 352 then
![634, 635]
else
(if i.val < 353 then
![636, 637]
else
![638, 639])))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
![640, 641]
else
![642, 643])
else
(if i.val < 357 then
![644, 645]
else
![576, 646]))
else
(if i.val < 360 then
(if i.val < 359 then
![423, 647]
else
![648, 649])
else
(if i.val < 361 then
![650, 275]
else
![651, 652])))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
![646, 653]
else
![654, 655])
else
(if i.val < 365 then
![656, 657]
else
![658, 659]))
else
(if i.val < 368 then
(if i.val < 367 then
![660, 661]
else
![425, 662])
else
(if i.val < 369 then
![663, 664]
else
(if i.val < 370 then
![665, 666]
else
![667, 668]))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
![669, 670]
else
![671, 672])
else
(if i.val < 374 then
![661, 673]
else
![674, 675]))
else
(if i.val < 377 then
(if i.val < 376 then
![676, 677]
else
![678, 679])
else
(if i.val < 378 then
![680, 681]
else
![60, 682])))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
![683, 684]
else
![685, 686])
else
(if i.val < 382 then
![427, 687]
else
![688, 689]))
else
(if i.val < 385 then
(if i.val < 384 then
![690, 691]
else
![692, 693])
else
(if i.val < 386 then
![694, 86]
else
(if i.val < 387 then
![695, 125]
else
![686, 696])))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
![697, 698]
else
![699, 700])
else
(if i.val < 391 then
![701, 671]
else
![702, 703]))
else
(if i.val < 394 then
(if i.val < 393 then
![704, 705]
else
![706, 707])
else
(if i.val < 395 then
![429, 708]
else
![533, 709])))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
![710, 711]
else
![712, 713])
else
(if i.val < 399 then
![714, 715]
else
![716, 717]))
else
(if i.val < 402 then
(if i.val < 401 then
![718, 719]
else
![707, 720])
else
(if i.val < 403 then
![579, 721]
else
(if i.val < 404 then
![722, 723]
else
![724, 99]))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
![725, 726]
else
![727, 728])
else
(if i.val < 408 then
![729, 730]
else
![731, 732]))
else
(if i.val < 411 then
(if i.val < 410 then
![4, 733]
else
![734, 735])
else
(if i.val < 412 then
![736, 112]
else
![611, 737])))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
![738, 739]
else
![740, 741])
else
(if i.val < 416 then
![742, 743]
else
![732, 744]))
else
(if i.val < 419 then
(if i.val < 418 then
![745, 746]
else
![747, 748])
else
(if i.val < 420 then
![749, 750]
else
![751, 752]))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
![68, 753]
else
![754, 755])
else
(if i.val < 424 then
![756, 757]
else
![6, 758]))
else
(if i.val < 427 then
(if i.val < 426 then
![759, 760]
else
![761, 762])
else
(if i.val < 428 then
![763, 764]
else
![81, 765])))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
![766, 767]
else
![757, 768])
else
(if i.val < 432 then
![619, 769]
else
![557, 770]))
else
(if i.val < 435 then
(if i.val < 434 then
![771, 742]
else
![772, 773])
else
(if i.val < 436 then
![774, 342]
else
(if i.val < 437 then
![775, 776]
else
![723, 777]))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
![778, 779]
else
![780, 781])
else
(if i.val < 441 then
![782, 368]
else
![783, 784]))
else
(if i.val < 444 then
(if i.val < 443 then
![785, 786]
else
![776, 787])
else
(if i.val < 445 then
![788, 789]
else
![790, 791])))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
![792, 793]
else
![705, 794])
else
(if i.val < 449 then
![795, 796]
else
![797, 798]))
else
(if i.val < 452 then
(if i.val < 451 then
![799, 800]
else
![801, 802])
else
(if i.val < 453 then
![803, 804]
else
(if i.val < 454 then
![371, 805]
else
![800, 806])))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
![807, 808]
else
![809, 810])
else
(if i.val < 458 then
![811, 812]
else
![726, 813]))
else
(if i.val < 461 then
(if i.val < 460 then
![814, 815]
else
![816, 817])
else
(if i.val < 462 then
![818, 819]
else
![820, 821])))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
![822, 823]
else
![812, 824])
else
(if i.val < 466 then
![825, 826]
else
![827, 354]))
else
(if i.val < 469 then
(if i.val < 468 then
![828, 829]
else
![830, 831])
else
(if i.val < 470 then
![832, 833]
else
(if i.val < 471 then
![728, 834]
else
![835, 836])))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
![837, 838]
else
![839, 840])
else
(if i.val < 475 then
![841, 842]
else
![305, 843]))
else
(if i.val < 478 then
(if i.val < 477 then
![833, 844]
else
![845, 846])
else
(if i.val < 479 then
![847, 848]
else
![849, 822])))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
![850, 851]
else
![852, 853])
else
(if i.val < 483 then
![854, 855]
else
![730, 856]))
else
(if i.val < 486 then
(if i.val < 485 then
![719, 857]
else
![858, 859])
else
(if i.val < 487 then
![860, 861]
else
(if i.val < 488 then
![862, 863]
else
![864, 865])))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
![866, 867]
else
![855, 868])
else
(if i.val < 492 then
![869, 870]
else
![871, 872]))
else
(if i.val < 495 then
(if i.val < 494 then
![873, 874]
else
![875, 876])
else
(if i.val < 496 then
![877, 878]
else
![879, 880])))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
![881, 882]
else
![882, 883])
else
(if i.val < 500 then
![733, 884]
else
![885, 886]))
else
(if i.val < 503 then
(if i.val < 502 then
![887, 888]
else
![856, 889])
else
(if i.val < 504 then
![890, 891]
else
(if i.val < 505 then
![892, 893]
else
![894, 895]))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
![744, 896]
else
![897, 898])
else
(if i.val < 509 then
![899, 900]
else
![83, 901]))
else
(if i.val < 512 then
(if i.val < 511 then
![902, 431]
else
![903, 904])
else
(if i.val < 513 then
![735, 905]
else
![906, 907])))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
![908, 909]
else
![910, 911])
else
(if i.val < 517 then
![912, 913]
else
![914, 915]))
else
(if i.val < 520 then
(if i.val < 519 then
![904, 916]
else
![917, 918])
else
(if i.val < 521 then
![919, 920]
else
(if i.val < 522 then
![921, 894]
else
![922, 923])))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
![924, 925]
else
![926, 927])
else
(if i.val < 526 then
![928, 929]
else
![817, 445]))
else
(if i.val < 529 then
(if i.val < 528 then
![930, 931]
else
![927, 932])
else
(if i.val < 530 then
![933, 934]
else
![935, 936])))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
![937, 190]
else
![938, 939])
else
(if i.val < 534 then
![940, 941]
else
![942, 943]))
else
(if i.val < 537 then
(if i.val < 536 then
![880, 944]
else
![737, 945])
else
(if i.val < 538 then
![946, 947]
else
(if i.val < 539 then
![948, 949]
else
![944, 950]))))))))))
else
(if i.val < 810 then
(if i.val < 675 then
(if i.val < 607 then
(if i.val < 573 then
(if i.val < 556 then
(if i.val < 548 then
(if i.val < 544 then
(if i.val < 542 then
(if i.val < 541 then
![951, 952]
else
![953, 954])
else
(if i.val < 543 then
![955, 956]
else
![957, 958]))
else
(if i.val < 546 then
(if i.val < 545 then
![739, 959]
else
![960, 961])
else
(if i.val < 547 then
![962, 963]
else
![964, 965])))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
![966, 967]
else
![968, 969])
else
(if i.val < 551 then
![958, 970]
else
![971, 972]))
else
(if i.val < 554 then
(if i.val < 553 then
![973, 974]
else
![975, 976])
else
(if i.val < 555 then
![977, 978]
else
![90, 979]))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
![980, 981]
else
![982, 983])
else
(if i.val < 559 then
![741, 984]
else
![985, 986]))
else
(if i.val < 562 then
(if i.val < 561 then
![987, 988]
else
![989, 990])
else
(if i.val < 563 then
![353, 142]
else
![991, 226])))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
![983, 992]
else
![993, 994])
else
(if i.val < 567 then
![995, 996]
else
![997, 968]))
else
(if i.val < 570 then
(if i.val < 569 then
![998, 999]
else
![1000, 1001])
else
(if i.val < 571 then
![1002, 1003]
else
(if i.val < 572 then
![743, 1004]
else
![838, 1005]))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
![1006, 1007]
else
![1008, 1009])
else
(if i.val < 576 then
![1010, 1011]
else
![1012, 1013]))
else
(if i.val < 579 then
(if i.val < 578 then
![1014, 1015]
else
![1003, 1016])
else
(if i.val < 580 then
![883, 1017]
else
![1018, 1019])))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
![1020, 1021]
else
![1022, 1023])
else
(if i.val < 584 then
![1024, 1025]
else
![96, 1026]))
else
(if i.val < 587 then
(if i.val < 586 then
![1027, 1028]
else
![746, 1029])
else
(if i.val < 588 then
![1030, 1031]
else
(if i.val < 589 then
![1032, 1033]
else
![1034, 1035])))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
![109, 1036]
else
![1037, 447])
else
(if i.val < 593 then
![1028, 1038]
else
![1039, 1040]))
else
(if i.val < 596 then
(if i.val < 595 then
![713, 1041]
else
![748, 1042])
else
(if i.val < 597 then
![1043, 985]
else
![1044, 1045])))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
![1046, 1047]
else
![1048, 1049])
else
(if i.val < 601 then
![874, 1050]
else
![1051, 1052]))
else
(if i.val < 604 then
(if i.val < 603 then
![1053, 1054]
else
![1055, 1056])
else
(if i.val < 605 then
![286, 1057]
else
(if i.val < 606 then
![1058, 1059]
else
![1060, 1061])))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
![1062, 1063]
else
![750, 1064])
else
(if i.val < 610 then
![1065, 1066]
else
![1067, 1068]))
else
(if i.val < 613 then
(if i.val < 612 then
![1069, 1070]
else
![1063, 1071])
else
(if i.val < 614 then
![1072, 1073]
else
![1074, 1075])))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
![1076, 1077]
else
![1078, 1079])
else
(if i.val < 618 then
![752, 1080]
else
![258, 1081]))
else
(if i.val < 621 then
(if i.val < 620 then
![1082, 1083]
else
![1084, 1085])
else
(if i.val < 622 then
![1086, 1087]
else
(if i.val < 623 then
![1088, 1089]
else
![1079, 1090])))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
![1091, 1092]
else
![1093, 1094])
else
(if i.val < 627 then
![1095, 1096]
else
![1097, 1098]))
else
(if i.val < 630 then
(if i.val < 629 then
![1099, 1100]
else
![753, 1101])
else
(if i.val < 631 then
![1102, 1103]
else
![1104, 1105])))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
![397, 1106]
else
![1100, 1107])
else
(if i.val < 635 then
![1108, 1109]
else
![1110, 1111]))
else
(if i.val < 638 then
(if i.val < 637 then
![299, 1088]
else
![1112, 1113])
else
(if i.val < 639 then
![1114, 1115]
else
(if i.val < 640 then
![128, 1116]
else
![755, 1117]))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
![1118, 1119]
else
![1120, 1121])
else
(if i.val < 644 then
![1122, 1123]
else
![1124, 1125]))
else
(if i.val < 647 then
(if i.val < 646 then
![1126, 567]
else
![1116, 1127])
else
(if i.val < 648 then
![1128, 1129]
else
![1130, 1131])))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
![1132, 1133]
else
![1134, 1135])
else
(if i.val < 652 then
![1136, 1137]
else
![1138, 1139]))
else
(if i.val < 655 then
(if i.val < 654 then
![1139, 1140]
else
![758, 1141])
else
(if i.val < 656 then
![1142, 1143]
else
(if i.val < 657 then
![1144, 1145]
else
![1117, 1146])))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
![1147, 1148]
else
![1149, 1150])
else
(if i.val < 661 then
![1151, 1152]
else
![768, 1153]))
else
(if i.val < 664 then
(if i.val < 663 then
![1154, 1155]
else
![1156, 910])
else
(if i.val < 665 then
![111, 470]
else
![1157, 593])))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
![1158, 1159]
else
![760, 1160])
else
(if i.val < 669 then
![1161, 3]
else
![1162, 1163]))
else
(if i.val < 672 then
(if i.val < 671 then
![1164, 1165]
else
![1166, 1167])
else
(if i.val < 673 then
![1168, 1169]
else
(if i.val < 674 then
![1159, 729]
else
![1170, 1171]))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
![1172, 512]
else
![1173, 1151])
else
(if i.val < 678 then
![133, 1174]
else
![1175, 1176]))
else
(if i.val < 681 then
(if i.val < 680 then
![1177, 1178]
else
![762, 1179])
else
(if i.val < 682 then
![1180, 1181]
else
![1182, 1183])))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
![1184, 1185]
else
![1083, 602])
else
(if i.val < 686 then
![1186, 1187]
else
![1178, 1188]))
else
(if i.val < 689 then
(if i.val < 688 then
![1189, 1190]
else
![1191, 1192])
else
(if i.val < 690 then
![1193, 1194]
else
![1195, 1196]))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
![1197, 1198]
else
![1199, 1200])
else
(if i.val < 694 then
![1137, 1201]
else
![764, 1202]))
else
(if i.val < 697 then
(if i.val < 696 then
![1203, 615]
else
![1201, 1204])
else
(if i.val < 698 then
![1205, 1206]
else
![1207, 1208])))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
![1209, 477]
else
![1210, 1211])
else
(if i.val < 702 then
![765, 1212]
else
![1213, 1214]))
else
(if i.val < 705 then
(if i.val < 704 then
![1215, 1216]
else
![1217, 1218])
else
(if i.val < 706 then
![1219, 1220]
else
(if i.val < 707 then
![824, 1221]
else
![1211, 1222]))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
![1223, 1224]
else
![1225, 1226])
else
(if i.val < 711 then
![1227, 1228]
else
![116, 1229]))
else
(if i.val < 714 then
(if i.val < 713 then
![160, 1230]
else
![1231, 1232])
else
(if i.val < 715 then
![767, 1233]
else
![1234, 1235])))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
![1236, 1237]
else
![1238, 241])
else
(if i.val < 719 then
![1239, 192]
else
![1240, 318]))
else
(if i.val < 722 then
(if i.val < 721 then
![1232, 1241]
else
![1140, 852])
else
(if i.val < 723 then
![1242, 1243]
else
(if i.val < 724 then
![1244, 1245]
else
![1246, 1219])))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
![8, 1247]
else
![1248, 1249])
else
(if i.val < 728 then
![1250, 167]
else
![915, 1251]))
else
(if i.val < 731 then
(if i.val < 730 then
![1252, 1253]
else
![1254, 1255])
else
(if i.val < 732 then
![1256, 1257]
else
![187, 1258])))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
![1259, 1260]
else
![1261, 1262])
else
(if i.val < 736 then
![1263, 1264]
else
![1265, 1266]))
else
(if i.val < 739 then
(if i.val < 738 then
![1267, 1268]
else
![10, 1269])
else
(if i.val < 740 then
![1270, 1271]
else
(if i.val < 741 then
![1272, 1273]
else
![1274, 638])))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
![137, 1275]
else
![1276, 1277])
else
(if i.val < 745 then
![1268, 1278]
else
![923, 1279]))
else
(if i.val < 748 then
(if i.val < 747 then
![861, 205]
else
![1280, 1256])
else
(if i.val < 749 then
![1281, 1282]
else
![1283, 523])))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
![1284, 1285]
else
![12, 1286])
else
(if i.val < 753 then
![1287, 1288]
else
![1169, 1289]))
else
(if i.val < 756 then
(if i.val < 755 then
![1290, 545]
else
![1291, 1292])
else
(if i.val < 757 then
![1293, 1294]
else
(if i.val < 758 then
![1285, 1295]
else
![1296, 1297])))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
![1298, 1299]
else
![1300, 1301])
else
(if i.val < 762 then
![1001, 1302]
else
![175, 1303]))
else
(if i.val < 765 then
(if i.val < 764 then
![1304, 1305]
else
![1306, 1307])
else
(if i.val < 766 then
![1308, 1309]
else
![1310, 1311])))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
![548, 1312]
else
![1307, 1313])
else
(if i.val < 770 then
![1314, 1315]
else
![1316, 1317]))
else
(if i.val < 773 then
(if i.val < 772 then
![1243, 1318]
else
![1319, 1320])
else
(if i.val < 774 then
![1321, 1322]
else
(if i.val < 775 then
![1228, 1323]
else
![1324, 1325]))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
![1317, 1326]
else
![1327, 1328])
else
(if i.val < 779 then
![1329, 532]
else
![1330, 1331]))
else
(if i.val < 782 then
(if i.val < 781 then
![1332, 1333]
else
![1334, 1335])
else
(if i.val < 783 then
![1245, 1336]
else
![1337, 1338])))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
![1339, 1340]
else
![1341, 1342])
else
(if i.val < 787 then
![486, 1343]
else
![1335, 1344]))
else
(if i.val < 790 then
(if i.val < 789 then
![1345, 1346]
else
![1347, 1348])
else
(if i.val < 791 then
![1129, 1324]
else
(if i.val < 792 then
![1349, 1350]
else
![1351, 1352])))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
![1353, 1354]
else
![1015, 1355])
else
(if i.val < 796 then
![1356, 1357]
else
![1358, 1359]))
else
(if i.val < 799 then
(if i.val < 798 then
![1360, 1361]
else
![1362, 1363])
else
(if i.val < 800 then
![1364, 1365]
else
![1354, 1051])))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
![1366, 1367]
else
![1368, 1369])
else
(if i.val < 804 then
![1370, 1371]
else
![1372, 363]))
else
(if i.val < 807 then
(if i.val < 806 then
![1373, 1374]
else
![1374, 1375])
else
(if i.val < 808 then
![1247, 1376]
else
(if i.val < 809 then
![1377, 1378]
else
![1379, 1380])))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
![1220, 1381]
else
![1382, 1383])
else
(if i.val < 813 then
![1258, 1384]
else
![1190, 1385]))
else
(if i.val < 816 then
(if i.val < 815 then
![1386, 1387]
else
![139, 1388])
else
(if i.val < 817 then
![1389, 745]
else
![1390, 1391])))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
![1249, 1392]
else
![1393, 1394])
else
(if i.val < 821 then
![1395, 1396]
else
![1397, 1398]))
else
(if i.val < 824 then
(if i.val < 823 then
![1399, 1400]
else
![1401, 1402])
else
(if i.val < 825 then
![1391, 1403]
else
![1404, 1405]))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
![1406, 1407]
else
![1408, 1382])
else
(if i.val < 829 then
![1409, 1410]
else
![1411, 1412]))
else
(if i.val < 832 then
(if i.val < 831 then
![1413, 1414]
else
![1322, 759])
else
(if i.val < 833 then
![1415, 1416]
else
![1412, 1417])))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
![587, 1418]
else
![1419, 606])
else
(if i.val < 837 then
![1420, 289]
else
![1421, 1422]))
else
(if i.val < 840 then
(if i.val < 839 then
![1423, 1424]
else
![1425, 1426])
else
(if i.val < 841 then
![670, 1427]
else
(if i.val < 842 then
![1251, 1428]
else
![1429, 1430]))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
![1431, 1432]
else
![1427, 1433])
else
(if i.val < 846 then
![1434, 1435]
else
![1436, 631]))
else
(if i.val < 849 then
(if i.val < 848 then
![1437, 1438]
else
![675, 1439])
else
(if i.val < 850 then
![1253, 1440]
else
![1441, 1442])))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
![687, 1443]
else
![1444, 1445])
else
(if i.val < 854 then
![1446, 1447]
else
![1448, 1449]))
else
(if i.val < 857 then
(if i.val < 856 then
![1439, 1450]
else
![1451, 710])
else
(if i.val < 858 then
![1452, 1453]
else
(if i.val < 859 then
![1454, 1455]
else
![146, 1456])))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
![1457, 1458]
else
![1459, 1460])
else
(if i.val < 863 then
![1255, 1461]
else
![1462, 1463]))
else
(if i.val < 866 then
(if i.val < 865 then
![1464, 1465]
else
![1466, 1467])
else
(if i.val < 867 then
![531, 243]
else
![1468, 409])))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
![1460, 1469]
else
![1470, 1471])
else
(if i.val < 871 then
![1472, 1473]
else
![1474, 1448]))
else
(if i.val < 874 then
(if i.val < 873 then
![1475, 1476]
else
![1477, 1478])
else
(if i.val < 875 then
![1479, 1480]
else
(if i.val < 876 then
![1257, 1481]
else
![1338, 1482])))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
![1483, 1484]
else
![1241, 1485])
else
(if i.val < 880 then
![1486, 1487]
else
![1488, 1489]))
else
(if i.val < 883 then
(if i.val < 882 then
![1490, 1491]
else
![1480, 1492])
else
(if i.val < 884 then
![1375, 1493]
else
![1494, 1495])))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
![1496, 1497]
else
![1498, 1499])
else
(if i.val < 888 then
![1500, 1501]
else
![152, 1502]))
else
(if i.val < 891 then
(if i.val < 890 then
![1503, 1504]
else
![1260, 1505])
else
(if i.val < 892 then
![362, 1506]
else
(if i.val < 893 then
![601, 1507]
else
![1508, 1509])))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
![164, 1510]
else
![1511, 761])
else
(if i.val < 897 then
![1504, 1512]
else
![1513, 1514]))
else
(if i.val < 900 then
(if i.val < 899 then
![1009, 1515]
else
![1262, 1516])
else
(if i.val < 901 then
![1517, 1462]
else
![1518, 367])))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
![1519, 1520]
else
![1521, 1522])
else
(if i.val < 905 then
![1369, 1523]
else
![1524, 1525]))
else
(if i.val < 908 then
(if i.val < 907 then
![1526, 1527]
else
![1528, 1529])
else
(if i.val < 909 then
![467, 1530]
else
(if i.val < 910 then
![1531, 1532]
else
![1533, 1534]))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
![1535, 1536]
else
![1264, 1537])
else
(if i.val < 914 then
![1538, 1539]
else
![1540, 1541]))
else
(if i.val < 917 then
(if i.val < 916 then
![1542, 1543]
else
![1536, 1544])
else
(if i.val < 918 then
![1545, 1546]
else
![614, 1547])))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
![1548, 1549]
else
![1550, 1551])
else
(if i.val < 922 then
![1266, 1552]
else
![441, 1553]))
else
(if i.val < 925 then
(if i.val < 924 then
![1554, 1555]
else
![1556, 1557])
else
(if i.val < 926 then
![1558, 1559]
else
(if i.val < 927 then
![1560, 1561]
else
![1551, 1562])))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
![211, 1563]
else
![1564, 1565])
else
(if i.val < 931 then
![1566, 1567]
else
![574, 1568]))
else
(if i.val < 934 then
(if i.val < 933 then
![218, 1569]
else
![1570, 1571])
else
(if i.val < 935 then
![1572, 1573]
else
![480, 1560])))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
![1574, 1575]
else
![1576, 1577])
else
(if i.val < 939 then
![1070, 1578]
else
![677, 1579]))
else
(if i.val < 942 then
(if i.val < 941 then
![1580, 1581]
else
![326, 1582])
else
(if i.val < 943 then
![1071, 1583]
else
(if i.val < 944 then
![1584, 871]
else
![351, 1585]))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
![1586, 1587]
else
![1588, 1589])
else
(if i.val < 948 then
![1590, 1591]
else
![1592, 1593]))
else
(if i.val < 951 then
(if i.val < 950 then
![1594, 1595]
else
![1595, 1596])
else
(if i.val < 952 then
![1269, 1597]
else
![1598, 1599])))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
![1600, 1601]
else
![1578, 1602])
else
(if i.val < 956 then
![1603, 1604]
else
![1605, 1606]))
else
(if i.val < 959 then
(if i.val < 958 then
![1607, 331]
else
![1278, 1608])
else
(if i.val < 960 then
![1609, 1610]
else
![1611, 1397]))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
![166, 782]
else
![1612, 897])
else
(if i.val < 964 then
![1613, 1614]
else
![1271, 1615]))
else
(if i.val < 967 then
(if i.val < 966 then
![1616, 7]
else
![1617, 1618])
else
(if i.val < 968 then
![1619, 1620]
else
![1621, 1622])))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
![1623, 388]
else
![1614, 1246])
else
(if i.val < 972 then
![1624, 702]
else
![1625, 818]))
else
(if i.val < 975 then
(if i.val < 974 then
![1626, 1607]
else
![234, 1627])
else
(if i.val < 976 then
![589, 1628]
else
(if i.val < 977 then
![1629, 1630]
else
![1273, 1631]))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
![1632, 108]
else
![1633, 1634])
else
(if i.val < 981 then
![1635, 1636]
else
![1555, 906]))
else
(if i.val < 984 then
(if i.val < 983 then
![1637, 1638]
else
![1630, 1639])
else
(if i.val < 985 then
![1640, 1641]
else
![1642, 1643])))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
![1644, 1645]
else
![1646, 1647])
else
(if i.val < 989 then
![1648, 1649]
else
![1650, 1651]))
else
(if i.val < 992 then
(if i.val < 991 then
![1593, 1652]
else
![1653, 919])
else
(if i.val < 993 then
![1652, 586]
else
(if i.val < 994 then
![1654, 1655]
else
![1656, 106])))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
![657, 788]
else
![1657, 1658])
else
(if i.val < 998 then
![1275, 1659]
else
![1660, 1661]))
else
(if i.val < 1001 then
(if i.val < 1000 then
![1662, 1043]
else
![1663, 1664])
else
(if i.val < 1002 then
![28, 1665]
else
![1326, 1666])))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
![1658, 383]
else
![1667, 1668])
else
(if i.val < 1006 then
![1669, 1670]
else
![1671, 1672]))
else
(if i.val < 1009 then
(if i.val < 1008 then
![171, 1673]
else
![261, 1674])
else
(if i.val < 1010 then
![1675, 1676]
else
(if i.val < 1011 then
![1277, 1677]
else
![1678, 1679])))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
![689, 333]
else
![1680, 424])
else
(if i.val < 1015 then
![1681, 291]
else
![1682, 499]))
else
(if i.val < 1018 then
(if i.val < 1017 then
![1676, 654]
else
![1596, 1351])
else
(if i.val < 1019 then
![1174, 1683]
else
![1123, 1684])))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
![981, 1293]
else
![1685, 1686])
else
(if i.val < 1023 then
![1687, 678]
else
![1688, 1689]))
else
(if i.val < 1026 then
(if i.val < 1025 then
![1279, 1690]
else
![1691, 1692])
else
(if i.val < 1027 then
![1693, 1694]
else
(if i.val < 1028 then
![1695, 1696]
else
![1689, 1697])))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
![1698, 1699]
else
![1700, 1701])
else
(if i.val < 1032 then
![1702, 1703]
else
![868, 1704]))
else
(if i.val < 1035 then
(if i.val < 1034 then
![1705, 1706]
else
![1707, 1708])
else
(if i.val < 1036 then
![1709, 1710]
else
![1711, 921])))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
![1712, 1713]
else
![1710, 1714])
else
(if i.val < 1040 then
![1715, 1716]
else
![1717, 1718]))
else
(if i.val < 1043 then
(if i.val < 1042 then
![1719, 1479]
else
![1501, 1720])
else
(if i.val < 1044 then
![1721, 690]
else
(if i.val < 1045 then
![1722, 1723]
else
![242, 1724]))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
![1282, 1725]
else
![1726, 1727])
else
(if i.val < 1049 then
![1333, 1728]
else
![643, 1729]))
else
(if i.val < 1052 then
(if i.val < 1051 then
![1724, 1730]
else
![1731, 1732])
else
(if i.val < 1053 then
![1733, 1734]
else
![1735, 1477])))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
![1736, 1737]
else
![1445, 1738])
else
(if i.val < 1057 then
![1739, 1740]
else
![1016, 1741]))
else
(if i.val < 1060 then
(if i.val < 1059 then
![1742, 1743]
else
![1744, 1745])
else
(if i.val < 1061 then
![1746, 1747]
else
(if i.val < 1062 then
![1748, 1749]
else
![1750, 1751])))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
![1740, 1752]
else
![1753, 1754])
else
(if i.val < 1066 then
![1400, 1755]
else
![1756, 1757]))
else
(if i.val < 1069 then
(if i.val < 1068 then
![1758, 1759]
else
![1760, 792])
else
(if i.val < 1070 then
![1761, 850]
else
![1762, 1763])))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
![1763, 1764]
else
![1286, 1765])
else
(if i.val < 1074 then
![1766, 1767]
else
![1768, 1769]))
else
(if i.val < 1077 then
(if i.val < 1076 then
![524, 1770]
else
![1771, 1772])
else
(if i.val < 1078 then
![1773, 1774]
else
(if i.val < 1079 then
![1775, 1776]
else
![1295, 1777])))))))))))
else
(if i.val < 1620 then
(if i.val < 1350 then
(if i.val < 1215 then
(if i.val < 1147 then
(if i.val < 1113 then
(if i.val < 1096 then
(if i.val < 1088 then
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
![1778, 1452]
else
![189, 1779])
else
(if i.val < 1083 then
![1780, 1018]
else
![1781, 1782]))
else
(if i.val < 1086 then
(if i.val < 1085 then
![1288, 1783]
else
![1784, 1785])
else
(if i.val < 1087 then
![559, 1786]
else
![1787, 1788])))
else
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
![1789, 1790]
else
![1791, 1792])
else
(if i.val < 1091 then
![1782, 1793]
else
![1794, 1795]))
else
(if i.val < 1094 then
(if i.val < 1093 then
![1796, 1797]
else
![1798, 1775])
else
(if i.val < 1095 then
![1348, 1799]
else
![1800, 1801]))))
else
(if i.val < 1104 then
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
![1802, 1803]
else
![1357, 1804])
else
(if i.val < 1099 then
![1473, 1030]
else
![1805, 1806]))
else
(if i.val < 1102 then
(if i.val < 1101 then
![1803, 1807]
else
![1808, 1809])
else
(if i.val < 1103 then
![1810, 1811]
else
![1559, 381])))
else
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
![1289, 1812]
else
![1813, 1814])
else
(if i.val < 1107 then
![1815, 1816]
else
![851, 1817]))
else
(if i.val < 1110 then
(if i.val < 1109 then
![1818, 1819]
else
![1820, 1821])
else
(if i.val < 1111 then
![1822, 1823]
else
(if i.val < 1112 then
![1824, 1825]
else
![1826, 1827]))))))
else
(if i.val < 1130 then
(if i.val < 1121 then
(if i.val < 1117 then
(if i.val < 1115 then
(if i.val < 1114 then
![1628, 1828]
else
![1829, 1830])
else
(if i.val < 1116 then
![1831, 1832]
else
![1825, 1833]))
else
(if i.val < 1119 then
(if i.val < 1118 then
![469, 1834]
else
![77, 1835])
else
(if i.val < 1120 then
![1836, 1837]
else
![1371, 1838])))
else
(if i.val < 1125 then
(if i.val < 1123 then
(if i.val < 1122 then
![196, 1839]
else
![1840, 1841])
else
(if i.val < 1124 then
![1842, 1843]
else
![1292, 1844]))
else
(if i.val < 1127 then
(if i.val < 1126 then
![1534, 1845]
else
![1426, 1846])
else
(if i.val < 1128 then
![1843, 1847]
else
(if i.val < 1129 then
![1848, 1849]
else
![1850, 1851])))))
else
(if i.val < 1138 then
(if i.val < 1134 then
(if i.val < 1132 then
(if i.val < 1131 then
![1852, 239]
else
![1561, 1853])
else
(if i.val < 1133 then
![1854, 1855]
else
![1856, 1857]))
else
(if i.val < 1136 then
(if i.val < 1135 then
![1294, 1858]
else
![808, 1859])
else
(if i.val < 1137 then
![1860, 1861]
else
![1862, 41])))
else
(if i.val < 1142 then
(if i.val < 1140 then
(if i.val < 1139 then
![279, 1863]
else
![1857, 1864])
else
(if i.val < 1141 then
![1764, 1865]
else
![1495, 1866]))
else
(if i.val < 1144 then
(if i.val < 1143 then
![1867, 1612]
else
![1868, 1869])
else
(if i.val < 1145 then
![1870, 1871]
else
(if i.val < 1146 then
![202, 772]
else
![1872, 1873])))))))
else
(if i.val < 1181 then
(if i.val < 1164 then
(if i.val < 1155 then
(if i.val < 1151 then
(if i.val < 1149 then
(if i.val < 1148 then
![1297, 1874]
else
![1875, 1876])
else
(if i.val < 1150 then
![1877, 1878]
else
![1879, 293]))
else
(if i.val < 1153 then
(if i.val < 1152 then
![215, 1880]
else
![236, 1032])
else
(if i.val < 1154 then
![1873, 1881]
else
![1882, 1883])))
else
(if i.val < 1159 then
(if i.val < 1157 then
(if i.val < 1156 then
![950, 1884]
else
![1299, 1885])
else
(if i.val < 1158 then
![1886, 1887]
else
![1888, 1889]))
else
(if i.val < 1161 then
(if i.val < 1160 then
![1757, 1890]
else
![1891, 1892])
else
(if i.val < 1162 then
![1394, 1893]
else
(if i.val < 1163 then
![626, 1894]
else
![1895, 1896])))))
else
(if i.val < 1172 then
(if i.val < 1168 then
(if i.val < 1166 then
(if i.val < 1165 then
![1463, 820]
else
![1897, 1252])
else
(if i.val < 1167 then
![1301, 1898]
else
![1899, 1900]))
else
(if i.val < 1170 then
(if i.val < 1169 then
![1901, 1902]
else
![1903, 1904])
else
(if i.val < 1171 then
![1315, 1905]
else
![1906, 1907])))
else
(if i.val < 1176 then
(if i.val < 1174 then
(if i.val < 1173 then
![495, 1908]
else
![1302, 1909])
else
(if i.val < 1175 then
![884, 1910]
else
![1911, 1912]))
else
(if i.val < 1178 then
(if i.val < 1177 then
![1913, 1914]
else
![1915, 862])
else
(if i.val < 1179 then
![905, 1916]
else
(if i.val < 1180 then
![1917, 1918]
else
![1919, 1920]))))))
else
(if i.val < 1198 then
(if i.val < 1189 then
(if i.val < 1185 then
(if i.val < 1183 then
(if i.val < 1182 then
![1921, 1922]
else
![1923, 1924])
else
(if i.val < 1184 then
![1925, 1926]
else
![1303, 1927]))
else
(if i.val < 1187 then
(if i.val < 1186 then
![1928, 1929]
else
![1930, 1931])
else
(if i.val < 1188 then
![539, 1932]
else
![1926, 1933])))
else
(if i.val < 1193 then
(if i.val < 1191 then
(if i.val < 1190 then
![1934, 1935]
else
![1936, 1937])
else
(if i.val < 1192 then
![637, 1915]
else
![1618, 1938]))
else
(if i.val < 1195 then
(if i.val < 1194 then
![1447, 1939]
else
![321, 1940])
else
(if i.val < 1196 then
![1305, 1941]
else
(if i.val < 1197 then
![1942, 1943]
else
![79, 1944])))))
else
(if i.val < 1206 then
(if i.val < 1202 then
(if i.val < 1200 then
(if i.val < 1199 then
![1945, 1946]
else
![1947, 1948])
else
(if i.val < 1201 then
![1949, 1130]
else
![1940, 1950]))
else
(if i.val < 1204 then
(if i.val < 1203 then
![72, 1951]
else
![1952, 1953])
else
(if i.val < 1205 then
![432, 1444]
else
![155, 1954])))
else
(if i.val < 1210 then
(if i.val < 1208 then
(if i.val < 1207 then
![1955, 1956]
else
![1957, 1958])
else
(if i.val < 1209 then
![1941, 1959]
else
![1553, 1960]))
else
(if i.val < 1212 then
(if i.val < 1211 then
![1581, 1961]
else
![1313, 1962])
else
(if i.val < 1213 then
![1963, 1964]
else
(if i.val < 1214 then
![1965, 1787]
else
![217, 1046]))))))))
else
(if i.val < 1282 then
(if i.val < 1248 then
(if i.val < 1231 then
(if i.val < 1223 then
(if i.val < 1219 then
(if i.val < 1217 then
(if i.val < 1216 then
![1966, 1154]
else
![1967, 1968])
else
(if i.val < 1218 then
![1309, 1969]
else
![1970, 11]))
else
(if i.val < 1221 then
(if i.val < 1220 then
![1971, 1972]
else
![1973, 1006])
else
(if i.val < 1222 then
![1974, 1975]
else
![1968, 1283])))
else
(if i.val < 1227 then
(if i.val < 1225 then
(if i.val < 1224 then
![1976, 1977]
else
![1978, 1084])
else
(if i.val < 1226 then
![1979, 1980]
else
![1981, 1982]))
else
(if i.val < 1229 then
(if i.val < 1228 then
![1311, 1983]
else
![1984, 1985])
else
(if i.val < 1230 then
![1986, 1987]
else
![1910, 1161]))))
else
(if i.val < 1239 then
(if i.val < 1235 then
(if i.val < 1233 then
(if i.val < 1232 then
![1988, 1989]
else
![1982, 1990])
else
(if i.val < 1234 then
![1991, 1992]
else
![1993, 1994]))
else
(if i.val < 1237 then
(if i.val < 1236 then
![1995, 995]
else
![1340, 1996])
else
(if i.val < 1238 then
![1997, 1998]
else
![1999, 2000])))
else
(if i.val < 1243 then
(if i.val < 1241 then
(if i.val < 1240 then
![1312, 2001]
else
![2002, 1172])
else
(if i.val < 1242 then
![444, 2003]
else
![16, 1780]))
else
(if i.val < 1245 then
(if i.val < 1244 then
![2004, 1984]
else
![2005, 268])
else
(if i.val < 1246 then
![1402, 2006]
else
(if i.val < 1247 then
![2007, 1850]
else
![2008, 1930]))))))
else
(if i.val < 1265 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
![2009, 2010]
else
![2011, 2012])
else
(if i.val < 1251 then
![2013, 2014]
else
![2015, 2016]))
else
(if i.val < 1254 then
(if i.val < 1253 then
![18, 2017]
else
![2018, 2019])
else
(if i.val < 1255 then
![2020, 2021]
else
![2022, 937])))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
![238, 2023]
else
![1992, 2024])
else
(if i.val < 1259 then
![2016, 2025]
else
![641, 2026]))
else
(if i.val < 1262 then
(if i.val < 1261 then
![1359, 304]
else
![2027, 344])
else
(if i.val < 1263 then
![2028, 2029]
else
(if i.val < 1264 then
![691, 828]
else
![2030, 2031])))))
else
(if i.val < 1273 then
(if i.val < 1269 then
(if i.val < 1267 then
(if i.val < 1266 then
![20, 2032]
else
![2033, 2034])
else
(if i.val < 1268 then
![2035, 1184]
else
![2031, 2036]))
else
(if i.val < 1271 then
(if i.val < 1270 then
![632, 2037]
else
![2038, 2039])
else
(if i.val < 1272 then
![2040, 2041]
else
![1478, 2042])))
else
(if i.val < 1277 then
(if i.val < 1275 then
(if i.val < 1274 then
![276, 2043]
else
![2044, 2045])
else
(if i.val < 1276 then
![2046, 2047]
else
![2048, 2049]))
else
(if i.val < 1279 then
(if i.val < 1278 then
![853, 2050]
else
![1115, 2051])
else
(if i.val < 1280 then
![2052, 2053]
else
(if i.val < 1281 then
![24, 2054]
else
![2055, 358])))))))
else
(if i.val < 1316 then
(if i.val < 1299 then
(if i.val < 1290 then
(if i.val < 1286 then
(if i.val < 1284 then
(if i.val < 1283 then
![1792, 2056]
else
![1672, 2057])
else
(if i.val < 1285 then
![2058, 2059]
else
![378, 2060]))
else
(if i.val < 1288 then
(if i.val < 1287 then
![2061, 2062]
else
![2063, 837])
else
(if i.val < 1289 then
![2064, 2065]
else
![2066, 2067])))
else
(if i.val < 1294 then
(if i.val < 1292 then
(if i.val < 1291 then
![26, 2068]
else
![2069, 2070])
else
(if i.val < 1293 then
![2071, 1193]
else
![328, 2072]))
else
(if i.val < 1296 then
(if i.val < 1295 then
![796, 2073]
else
![2067, 2074])
else
(if i.val < 1297 then
![1799, 2075]
else
(if i.val < 1298 then
![1745, 396]
else
![1587, 2058])))))
else
(if i.val < 1307 then
(if i.val < 1303 then
(if i.val < 1301 then
(if i.val < 1300 then
![2076, 2077]
else
![2078, 1095])
else
(if i.val < 1302 then
![2079, 2080]
else
![1491, 2081]))
else
(if i.val < 1305 then
(if i.val < 1304 then
![1975, 2082]
else
![2083, 1112])
else
(if i.val < 1306 then
![2084, 2085]
else
![2086, 2087])))
else
(if i.val < 1311 then
(if i.val < 1309 then
(if i.val < 1308 then
![2080, 1524]
else
![2088, 2089])
else
(if i.val < 1310 then
![2090, 2091]
else
![1855, 2092]))
else
(if i.val < 1313 then
(if i.val < 1312 then
![366, 540]
else
![2093, 2094])
else
(if i.val < 1314 then
![2094, 2095]
else
(if i.val < 1315 then
![2096, 2097]
else
![1665, 2098]))))))
else
(if i.val < 1333 then
(if i.val < 1324 then
(if i.val < 1320 then
(if i.val < 1318 then
(if i.val < 1317 then
![2099, 2100]
else
![346, 2101])
else
(if i.val < 1319 then
![1641, 2102]
else
![2103, 2104]))
else
(if i.val < 1322 then
(if i.val < 1321 then
![240, 2105]
else
![2106, 1259])
else
(if i.val < 1323 then
![2107, 2108]
else
![2109, 2110])))
else
(if i.val < 1328 then
(if i.val < 1326 then
(if i.val < 1325 then
![2111, 2112]
else
![1881, 52])
else
(if i.val < 1327 then
![2108, 2113]
else
![2114, 2115]))
else
(if i.val < 1330 then
(if i.val < 1329 then
![2116, 2117]
else
![2118, 2099])
else
(if i.val < 1331 then
![2119, 1191]
else
(if i.val < 1332 then
![2120, 2121]
else
![2122, 2123])))))
else
(if i.val < 1341 then
(if i.val < 1337 then
(if i.val < 1335 then
(if i.val < 1334 then
![2056, 1270]
else
![1816, 197])
else
(if i.val < 1336 then
![2121, 2124]
else
![891, 2125]))
else
(if i.val < 1339 then
(if i.val < 1338 then
![2126, 172]
else
![2127, 2128])
else
(if i.val < 1340 then
![2129, 2130]
else
![967, 2131])))
else
(if i.val < 1345 then
(if i.val < 1343 then
(if i.val < 1342 then
![2006, 2132]
else
![2133, 2134])
else
(if i.val < 1344 then
![2135, 598]
else
![2131, 2136]))
else
(if i.val < 1347 then
(if i.val < 1346 then
![2137, 2138]
else
![2139, 930])
else
(if i.val < 1348 then
![2140, 2141]
else
(if i.val < 1349 then
![972, 2142]
else
![2143, 2144])))))))))
else
(if i.val < 1485 then
(if i.val < 1417 then
(if i.val < 1383 then
(if i.val < 1366 then
(if i.val < 1358 then
(if i.val < 1354 then
(if i.val < 1352 then
(if i.val < 1351 then
![984, 2145]
else
![1029, 2146])
else
(if i.val < 1353 then
![2147, 2148]
else
![2149, 2150]))
else
(if i.val < 1356 then
(if i.val < 1355 then
![2142, 2151]
else
![2152, 2153])
else
(if i.val < 1357 then
![2154, 2155]
else
![247, 2156])))
else
(if i.val < 1362 then
(if i.val < 1360 then
(if i.val < 1359 then
![2157, 2158]
else
![1111, 1731])
else
(if i.val < 1361 then
![1972, 2159]
else
![2160, 2161]))
else
(if i.val < 1364 then
(if i.val < 1363 then
![2162, 179]
else
![2163, 2164])
else
(if i.val < 1365 then
![836, 426]
else
![2165, 725]))))
else
(if i.val < 1374 then
(if i.val < 1370 then
(if i.val < 1368 then
(if i.val < 1367 then
![2166, 2149]
else
![2167, 2168])
else
(if i.val < 1369 then
![2169, 2170]
else
![2171, 2172]))
else
(if i.val < 1372 then
(if i.val < 1371 then
![345, 2173]
else
![2070, 2174])
else
(if i.val < 1373 then
![2175, 2176]
else
![2177, 2178])))
else
(if i.val < 1378 then
(if i.val < 1376 then
(if i.val < 1375 then
![2172, 2179]
else
![2095, 2180])
else
(if i.val < 1377 then
![1835, 2181]
else
![2182, 2183]))
else
(if i.val < 1380 then
(if i.val < 1379 then
![1080, 2184]
else
![2185, 2186])
else
(if i.val < 1381 then
![253, 2187]
else
(if i.val < 1382 then
![1101, 2188]
else
![265, 2189]))))))
else
(if i.val < 1400 then
(if i.val < 1391 then
(if i.val < 1387 then
(if i.val < 1385 then
(if i.val < 1384 then
![2190, 1272]
else
![2188, 2191])
else
(if i.val < 1386 then
![1485, 2192]
else
![2010, 2193]))
else
(if i.val < 1389 then
(if i.val < 1388 then
![2194, 2160]
else
![2195, 544])
else
(if i.val < 1390 then
![2196, 2197]
else
![2198, 2199])))
else
(if i.val < 1395 then
(if i.val < 1393 then
(if i.val < 1392 then
![2091, 2200]
else
![1832, 2201])
else
(if i.val < 1394 then
![2202, 2203]
else
![2204, 2205]))
else
(if i.val < 1397 then
(if i.val < 1396 then
![779, 2206]
else
![2207, 2208])
else
(if i.val < 1398 then
![382, 2209]
else
(if i.val < 1399 then
![2210, 2211]
else
![2012, 2212])))))
else
(if i.val < 1408 then
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
![2213, 2214]
else
![359, 2215])
else
(if i.val < 1403 then
![2216, 2217]
else
![2211, 2218]))
else
(if i.val < 1406 then
(if i.val < 1405 then
![2219, 2220]
else
![918, 2221])
else
(if i.val < 1407 then
![1040, 2222]
else
![2223, 2224])))
else
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
![2014, 2225]
else
![2226, 2227])
else
(if i.val < 1411 then
![2228, 2229]
else
![2230, 2231]))
else
(if i.val < 1414 then
(if i.val < 1413 then
![2224, 2232]
else
![310, 2233])
else
(if i.val < 1415 then
![2234, 1177]
else
(if i.val < 1416 then
![2235, 2236]
else
![878, 2237])))))))
else
(if i.val < 1451 then
(if i.val < 1434 then
(if i.val < 1425 then
(if i.val < 1421 then
(if i.val < 1419 then
(if i.val < 1418 then
![317, 1886]
else
![2238, 2239])
else
(if i.val < 1420 then
![791, 2230]
else
![2240, 1099]))
else
(if i.val < 1423 then
(if i.val < 1422 then
![1543, 1104]
else
![974, 2241])
else
(if i.val < 1424 then
![2242, 2243]
else
![507, 2244])))
else
(if i.val < 1429 then
(if i.val < 1427 then
(if i.val < 1426 then
![1544, 2245]
else
![2246, 1366])
else
(if i.val < 1428 then
![529, 1963]
else
![2247, 2248]))
else
(if i.val < 1431 then
(if i.val < 1430 then
![336, 2249]
else
![2250, 2251])
else
(if i.val < 1432 then
![2252, 2253]
else
(if i.val < 1433 then
![2254, 2255]
else
![2255, 2256])))))
else
(if i.val < 1442 then
(if i.val < 1438 then
(if i.val < 1436 then
(if i.val < 1435 then
![2017, 2257]
else
![2258, 2259])
else
(if i.val < 1437 then
![1073, 2260]
else
![2261, 2262]))
else
(if i.val < 1440 then
(if i.val < 1439 then
![2263, 2264]
else
![2025, 2265])
else
(if i.val < 1441 then
![2266, 2267]
else
![1845, 1086])))
else
(if i.val < 1446 then
(if i.val < 1444 then
(if i.val < 1443 then
![267, 1290]
else
![2268, 2269])
else
(if i.val < 1445 then
![2019, 2270]
else
![2271, 15]))
else
(if i.val < 1448 then
(if i.val < 1447 then
![2272, 2273]
else
![2274, 2275])
else
(if i.val < 1449 then
![2276, 2277]
else
(if i.val < 1450 then
![2278, 565]
else
![2269, 27]))))))
else
(if i.val < 1468 then
(if i.val < 1459 then
(if i.val < 1455 then
(if i.val < 1453 then
(if i.val < 1452 then
![2279, 998]
else
![893, 2280])
else
(if i.val < 1454 then
![2281, 2282]
else
![2021, 2283]))
else
(if i.val < 1457 then
(if i.val < 1456 then
![2284, 163]
else
![2285, 2286])
else
(if i.val < 1458 then
![2287, 2288]
else
![1119, 1393])))
else
(if i.val < 1463 then
(if i.val < 1461 then
(if i.val < 1460 then
![2289, 2290]
else
![2282, 2291])
else
(if i.val < 1462 then
![2292, 2293]
else
![334, 1215]))
else
(if i.val < 1465 then
(if i.val < 1464 then
![2294, 2295]
else
![2296, 2297])
else
(if i.val < 1466 then
![1152, 2298]
else
(if i.val < 1467 then
![2299, 181]
else
![2253, 2300])))))
else
(if i.val < 1476 then
(if i.val < 1472 then
(if i.val < 1470 then
(if i.val < 1469 then
![2301, 1406]
else
![2300, 890])
else
(if i.val < 1471 then
![2302, 2303]
else
![330, 161]))
else
(if i.val < 1474 then
(if i.val < 1473 then
![954, 1296]
else
![2304, 2305])
else
(if i.val < 1475 then
![2023, 2306]
else
![2307, 2308])))
else
(if i.val < 1480 then
(if i.val < 1478 then
(if i.val < 1477 then
![2309, 1517]
else
![2310, 2311])
else
(if i.val < 1479 then
![44, 2312]
else
![2060, 2313]))
else
(if i.val < 1482 then
(if i.val < 1481 then
![2305, 560]
else
![2314, 2315])
else
(if i.val < 1483 then
![2316, 2317]
else
(if i.val < 1484 then
![2318, 1197]
else
![272, 2319]))))))))
else
(if i.val < 1552 then
(if i.val < 1518 then
(if i.val < 1501 then
(if i.val < 1493 then
(if i.val < 1489 then
(if i.val < 1487 then
(if i.val < 1486 then
![2320, 2321]
else
![2024, 2322])
else
(if i.val < 1488 then
![2323, 2324]
else
![986, 514]))
else
(if i.val < 1491 then
(if i.val < 1490 then
![2325, 738]
else
![2326, 472])
else
(if i.val < 1492 then
![2327, 807]
else
![2321, 951])))
else
(if i.val < 1497 then
(if i.val < 1495 then
(if i.val < 1494 then
![2256, 2078]
else
![1627, 2328])
else
(if i.val < 1496 then
![1582, 2329]
else
![1458, 2035]))
else
(if i.val < 1499 then
(if i.val < 1498 then
![2330, 2331]
else
![1914, 975])
else
(if i.val < 1500 then
![2332, 2333]
else
![2026, 2334]))))
else
(if i.val < 1509 then
(if i.val < 1505 then
(if i.val < 1503 then
(if i.val < 1502 then
![2335, 2336]
else
![2337, 2338])
else
(if i.val < 1504 then
![2339, 2340]
else
![2333, 2341]))
else
(if i.val < 1507 then
(if i.val < 1506 then
![107, 2342]
else
![2343, 1168])
else
(if i.val < 1508 then
![2344, 2345]
else
![2346, 2347])))
else
(if i.val < 1513 then
(if i.val < 1511 then
(if i.val < 1510 then
![2348, 2349]
else
![2350, 1408])
else
(if i.val < 1512 then
![2351, 2352]
else
![2349, 1911]))
else
(if i.val < 1515 then
(if i.val < 1514 then
![2353, 2354]
else
![2355, 2356])
else
(if i.val < 1516 then
![2357, 2171]
else
(if i.val < 1517 then
![2186, 2358]
else
![2359, 987]))))))
else
(if i.val < 1535 then
(if i.val < 1526 then
(if i.val < 1522 then
(if i.val < 1520 then
(if i.val < 1519 then
![2360, 2361]
else
![2029, 2362])
else
(if i.val < 1521 then
![2363, 2364]
else
![1904, 2365]))
else
(if i.val < 1524 then
(if i.val < 1523 then
![941, 2366]
else
![662, 2367])
else
(if i.val < 1525 then
![2368, 2369]
else
![2370, 2371])))
else
(if i.val < 1530 then
(if i.val < 1528 then
(if i.val < 1527 then
![1889, 2169]
else
![1206, 2372])
else
(if i.val < 1529 then
![2146, 2373]
else
![2374, 2375]))
else
(if i.val < 1532 then
(if i.val < 1531 then
![1492, 2376]
else
![2377, 2378])
else
(if i.val < 1533 then
![2379, 2380]
else
(if i.val < 1534 then
![2381, 1236]
else
![2382, 2383])))))
else
(if i.val < 1543 then
(if i.val < 1539 then
(if i.val < 1537 then
(if i.val < 1536 then
![2384, 2385]
else
![2375, 2386])
else
(if i.val < 1538 then
![2387, 2388]
else
![2112, 2389]))
else
(if i.val < 1541 then
(if i.val < 1540 then
![2390, 2391]
else
![2392, 2393])
else
(if i.val < 1542 then
![2394, 1300]
else
![1202, 1349])))
else
(if i.val < 1547 then
(if i.val < 1545 then
(if i.val < 1544 then
![2395, 2396]
else
![2396, 2397])
else
(if i.val < 1546 then
![2032, 2398]
else
![2399, 2400]))
else
(if i.val < 1549 then
(if i.val < 1548 then
![829, 2401]
else
![2402, 2403])
else
(if i.val < 1550 then
![2404, 2405]
else
(if i.val < 1551 then
![395, 2406]
else
![2036, 2407])))))))
else
(if i.val < 1586 then
(if i.val < 1569 then
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
![2408, 2152]
else
![288, 2409])
else
(if i.val < 1555 then
![47, 1494]
else
![2410, 2411]))
else
(if i.val < 1558 then
(if i.val < 1557 then
![2034, 2412]
else
![1041, 2413])
else
(if i.val < 1559 then
![863, 2414]
else
![2415, 2416])))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
![2417, 2418]
else
![2419, 2420])
else
(if i.val < 1563 then
![2411, 2421]
else
![2422, 2423]))
else
(if i.val < 1566 then
(if i.val < 1565 then
![2424, 2425]
else
![2229, 558])
else
(if i.val < 1567 then
![389, 2426]
else
(if i.val < 1568 then
![2427, 2428]
else
![2429, 2430])))))
else
(if i.val < 1577 then
(if i.val < 1573 then
(if i.val < 1571 then
(if i.val < 1570 then
![1350, 2431]
else
![2432, 2433])
else
(if i.val < 1572 then
![2434, 2435]
else
![2436, 2437]))
else
(if i.val < 1575 then
(if i.val < 1574 then
![2438, 634]
else
![2439, 2440])
else
(if i.val < 1576 then
![2280, 2441]
else
![2442, 2443])))
else
(if i.val < 1581 then
(if i.val < 1579 then
(if i.val < 1578 then
![2444, 2445]
else
![781, 2446])
else
(if i.val < 1580 then
![2447, 2448]
else
![2092, 2449]))
else
(if i.val < 1583 then
(if i.val < 1582 then
![295, 2450]
else
![1765, 2451])
else
(if i.val < 1584 then
![2209, 2452]
else
(if i.val < 1585 then
![2130, 1794]
else
![2451, 1970]))))))
else
(if i.val < 1603 then
(if i.val < 1594 then
(if i.val < 1590 then
(if i.val < 1588 then
(if i.val < 1587 then
![2453, 2454]
else
![55, 2455])
else
(if i.val < 1589 then
![1987, 422]
else
![2231, 207]))
else
(if i.val < 1592 then
(if i.val < 1591 then
![2456, 2457]
else
![2458, 2459])
else
(if i.val < 1593 then
![2460, 2461]
else
![2462, 71])))
else
(if i.val < 1598 then
(if i.val < 1596 then
(if i.val < 1595 then
![460, 1733]
else
![2459, 2463])
else
(if i.val < 1597 then
![2397, 2464]
else
![2181, 2465]))
else
(if i.val < 1600 then
(if i.val < 1599 then
![2466, 1189]
else
![2467, 2468])
else
(if i.val < 1601 then
![2469, 2470]
else
(if i.val < 1602 then
![301, 1281]
else
![2471, 2472])))))
else
(if i.val < 1611 then
(if i.val < 1607 then
(if i.val < 1605 then
(if i.val < 1604 then
![2037, 2473]
else
![2474, 2475])
else
(if i.val < 1606 then
![2476, 2477]
else
![1135, 474]))
else
(if i.val < 1609 then
(if i.val < 1608 then
![314, 2478]
else
![2472, 2479])
else
(if i.val < 1610 then
![1021, 2480]
else
![1433, 1234])))
else
(if i.val < 1615 then
(if i.val < 1613 then
(if i.val < 1612 then
![2039, 2481]
else
![2482, 2483])
else
(if i.val < 1614 then
![2484, 2485]
else
![2391, 2486]))
else
(if i.val < 1617 then
(if i.val < 1616 then
![2487, 2488]
else
![2110, 2489])
else
(if i.val < 1618 then
![115, 2490]
else
(if i.val < 1619 then
![2491, 2492]
else
![2161, 620]))))))))))
else
(if i.val < 1890 then
(if i.val < 1755 then
(if i.val < 1687 then
(if i.val < 1653 then
(if i.val < 1636 then
(if i.val < 1628 then
(if i.val < 1624 then
(if i.val < 1622 then
(if i.val < 1621 then
![2493, 2007]
else
![2041, 177])
else
(if i.val < 1623 then
![2494, 2495]
else
![2496, 2497]))
else
(if i.val < 1626 then
(if i.val < 1625 then
![2053, 2498]
else
![804, 2499])
else
(if i.val < 1627 then
![2042, 2500]
else
![1376, 2501])))
else
(if i.val < 1632 then
(if i.val < 1630 then
(if i.val < 1629 then
![2502, 1778]
else
![2503, 1360])
else
(if i.val < 1631 then
![1392, 2504]
else
![2505, 2506]))
else
(if i.val < 1634 then
(if i.val < 1633 then
![2507, 2508]
else
![2509, 2510])
else
(if i.val < 1635 then
![2511, 2512]
else
![2043, 2513]))))
else
(if i.val < 1644 then
(if i.val < 1640 then
(if i.val < 1638 then
(if i.val < 1637 then
![2514, 2515]
else
![2516, 2517])
else
(if i.val < 1639 then
![844, 2518]
else
![2512, 2519]))
else
(if i.val < 1642 then
(if i.val < 1641 then
![1962, 2520]
else
![1049, 2521])
else
(if i.val < 1643 then
![936, 2503]
else
![2273, 2522])))
else
(if i.val < 1648 then
(if i.val < 1646 then
(if i.val < 1645 then
![2148, 1818]
else
![502, 2523])
else
(if i.val < 1647 then
![2045, 199]
else
![2524, 2525]))
else
(if i.val < 1650 then
(if i.val < 1649 then
![135, 2526]
else
![2527, 2528])
else
(if i.val < 1651 then
![2529, 2530]
else
(if i.val < 1652 then
![2531, 1588]
else
![2523, 2532]))))))
else
(if i.val < 1670 then
(if i.val < 1661 then
(if i.val < 1657 then
(if i.val < 1655 then
(if i.val < 1654 then
![2533, 2534]
else
![256, 1027])
else
(if i.val < 1656 then
![2535, 2536]
else
![2537, 2538]))
else
(if i.val < 1659 then
(if i.val < 1658 then
![2243, 2539]
else
![2051, 2540])
else
(if i.val < 1660 then
![2541, 2542]
else
![2543, 2415])))
else
(if i.val < 1665 then
(if i.val < 1663 then
(if i.val < 1662 then
![316, 1519]
else
![2544, 1609])
else
(if i.val < 1664 then
![2047, 2545]
else
![2546, 19]))
else
(if i.val < 1667 then
(if i.val < 1666 then
![2547, 1483]
else
![2548, 2549])
else
(if i.val < 1668 then
![1033, 2550]
else
(if i.val < 1669 then
![2551, 1556]
else
![2552, 2553])))))
else
(if i.val < 1678 then
(if i.val < 1674 then
(if i.val < 1672 then
(if i.val < 1671 then
![2554, 2555]
else
![2049, 1132])
else
(if i.val < 1673 then
![49, 2556]
else
![2557, 610]))
else
(if i.val < 1676 then
(if i.val < 1675 then
![2501, 1616]
else
![2558, 2559])
else
(if i.val < 1677 then
![2555, 1978]
else
![2560, 625])))
else
(if i.val < 1682 then
(if i.val < 1680 then
(if i.val < 1679 then
![2561, 2562]
else
![2563, 1472])
else
(if i.val < 1681 then
![2564, 1796]
else
![2050, 1138]))
else
(if i.val < 1684 then
(if i.val < 1683 then
![2565, 1625]
else
![2566, 2567])
else
(if i.val < 1685 then
![1004, 2568]
else
(if i.val < 1686 then
![2569, 2570]
else
![2571, 2572])))))))
else
(if i.val < 1721 then
(if i.val < 1704 then
(if i.val < 1695 then
(if i.val < 1691 then
(if i.val < 1689 then
(if i.val < 1688 then
![1562, 2573]
else
![2574, 2575])
else
(if i.val < 1690 then
![2568, 2576]
else
![2577, 2578]))
else
(if i.val < 1693 then
(if i.val < 1692 then
![2579, 903]
else
![2580, 2581])
else
(if i.val < 1694 then
![2189, 2582]
else
![969, 2583])))
else
(if i.val < 1699 then
(if i.val < 1697 then
(if i.val < 1696 then
![2584, 2585]
else
![1059, 2320])
else
(if i.val < 1698 then
![2583, 2586]
else
![2587, 2588]))
else
(if i.val < 1701 then
(if i.val < 1700 then
![2589, 2590]
else
![1951, 2574])
else
(if i.val < 1702 then
![2591, 2592]
else
(if i.val < 1703 then
![2593, 156]
else
![2594, 2595])))))
else
(if i.val < 1712 then
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
![1863, 2596]
else
![2597, 2598])
else
(if i.val < 1707 then
![2599, 2600]
else
![2601, 2602]))
else
(if i.val < 1710 then
(if i.val < 1709 then
![2603, 2604]
else
![2605, 2458])
else
(if i.val < 1711 then
![2595, 1891]
else
![2187, 2606])))
else
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
![2607, 151]
else
![2608, 697])
else
(if i.val < 1715 then
![1355, 2609]
else
![2054, 2610]))
else
(if i.val < 1718 then
(if i.val < 1717 then
![2611, 2612]
else
![2613, 2614])
else
(if i.val < 1719 then
![1469, 2460]
else
(if i.val < 1720 then
![2615, 2616]
else
![2617, 2447]))))))
else
(if i.val < 1738 then
(if i.val < 1729 then
(if i.val < 1725 then
(if i.val < 1723 then
(if i.val < 1722 then
![2618, 2615]
else
![2619, 2620])
else
(if i.val < 1724 then
![2572, 1308]
else
![2522, 2621]))
else
(if i.val < 1727 then
(if i.val < 1726 then
![1148, 2622]
else
![2623, 1164])
else
(if i.val < 1728 then
![2624, 629]
else
![2625, 2626])))
else
(if i.val < 1733 then
(if i.val < 1731 then
(if i.val < 1730 then
![2627, 2628]
else
![1381, 1613])
else
(if i.val < 1732 then
![2629, 2630]
else
![2631, 1186]))
else
(if i.val < 1735 then
(if i.val < 1734 then
![2632, 1545]
else
![1224, 2633])
else
(if i.val < 1736 then
![2057, 2634]
else
(if i.val < 1737 then
![2635, 2281]
else
![1233, 2636])))))
else
(if i.val < 1746 then
(if i.val < 1742 then
(if i.val < 1740 then
(if i.val < 1739 then
![2637, 2638]
else
![2214, 2639])
else
(if i.val < 1741 then
![2633, 2009]
else
![2640, 2641]))
else
(if i.val < 1744 then
(if i.val < 1743 then
![2642, 466]
else
![337, 2643])
else
(if i.val < 1745 then
![2644, 2429]
else
![2645, 2646])))
else
(if i.val < 1750 then
(if i.val < 1748 then
(if i.val < 1747 then
![925, 2647]
else
![840, 2648])
else
(if i.val < 1749 then
![2649, 2650]
else
![2651, 1572]))
else
(if i.val < 1752 then
(if i.val < 1751 then
![1103, 588]
else
![2553, 751])
else
(if i.val < 1753 then
![2646, 2652]
else
(if i.val < 1754 then
![2283, 2653]
else
![2654, 2655]))))))))
else
(if i.val < 1822 then
(if i.val < 1788 then
(if i.val < 1771 then
(if i.val < 1763 then
(if i.val < 1759 then
(if i.val < 1757 then
(if i.val < 1756 then
![2656, 2657]
else
![2205, 2658])
else
(if i.val < 1758 then
![2659, 2660]
else
![2059, 2661]))
else
(if i.val < 1761 then
(if i.val < 1760 then
![2499, 2662]
else
![2663, 2664])
else
(if i.val < 1762 then
![42, 2665]
else
![2666, 2667])))
else
(if i.val < 1767 then
(if i.val < 1765 then
(if i.val < 1764 then
![2660, 1644]
else
![2609, 2202])
else
(if i.val < 1766 then
![2668, 2669]
else
![1568, 2670]))
else
(if i.val < 1769 then
(if i.val < 1768 then
![2671, 2374]
else
![2672, 2673])
else
(if i.val < 1770 then
![343, 2674]
else
![2675, 2676]))))
else
(if i.val < 1779 then
(if i.val < 1775 then
(if i.val < 1773 then
(if i.val < 1772 then
![2062, 2677]
else
![696, 2678])
else
(if i.val < 1774 then
![1160, 2679]
else
![2680, 1316]))
else
(if i.val < 1777 then
(if i.val < 1776 then
![355, 2681]
else
![2682, 1310])
else
(if i.val < 1778 then
![2676, 2683]
else
![2684, 2685])))
else
(if i.val < 1783 then
(if i.val < 1781 then
(if i.val < 1780 then
![2686, 701]
else
![2687, 2516])
else
(if i.val < 1782 then
![2688, 2689]
else
![1552, 2690]))
else
(if i.val < 1785 then
(if i.val < 1784 then
![2691, 2692]
else
![2693, 1002])
else
(if i.val < 1786 then
![2694, 2695]
else
(if i.val < 1787 then
![2696, 2697]
else
![976, 2698]))))))
else
(if i.val < 1805 then
(if i.val < 1796 then
(if i.val < 1792 then
(if i.val < 1790 then
(if i.val < 1789 then
![2699, 2700]
else
![2065, 2701])
else
(if i.val < 1791 then
![2702, 2703]
else
![2704, 2705]))
else
(if i.val < 1794 then
(if i.val < 1793 then
![2706, 2008]
else
![2700, 2185])
else
(if i.val < 1795 then
![2707, 2708]
else
![1171, 2561])))
else
(if i.val < 1800 then
(if i.val < 1798 then
(if i.val < 1797 then
![2709, 483]
else
![2378, 2710])
else
(if i.val < 1799 then
![246, 2711]
else
![2712, 2713]))
else
(if i.val < 1802 then
(if i.val < 1801 then
![2714, 2544]
else
![2715, 2716])
else
(if i.val < 1803 then
![2717, 552]
else
(if i.val < 1804 then
![2710, 2718]
else
![2538, 2719])))))
else
(if i.val < 1813 then
(if i.val < 1809 then
(if i.val < 1807 then
(if i.val < 1806 then
![2176, 2720]
else
![504, 2721])
else
(if i.val < 1808 then
![402, 2722]
else
![2723, 2724]))
else
(if i.val < 1811 then
(if i.val < 1810 then
![2208, 1598]
else
![1054, 2717])
else
(if i.val < 1812 then
![2725, 2726]
else
![2727, 2728])))
else
(if i.val < 1817 then
(if i.val < 1815 then
(if i.val < 1814 then
![2542, 2729]
else
![2730, 2731])
else
(if i.val < 1816 then
![2732, 1621]
else
![2733, 2734]))
else
(if i.val < 1819 then
(if i.val < 1818 then
![2734, 2735]
else
![2068, 2736])
else
(if i.val < 1820 then
![2197, 2737]
else
(if i.val < 1821 then
![2738, 2216]
else
![2365, 2739])))))))
else
(if i.val < 1856 then
(if i.val < 1839 then
(if i.val < 1830 then
(if i.val < 1826 then
(if i.val < 1824 then
(if i.val < 1823 then
![2740, 2741]
else
![2742, 2743])
else
(if i.val < 1825 then
![148, 667]
else
![2074, 2744]))
else
(if i.val < 1828 then
(if i.val < 1827 then
![821, 2309]
else
![357, 1624])
else
(if i.val < 1829 then
![2461, 2745]
else
![961, 1254])))
else
(if i.val < 1834 then
(if i.val < 1832 then
(if i.val < 1831 then
![2345, 23]
else
![1007, 2746])
else
(if i.val < 1833 then
![2747, 2748]
else
![2745, 1459]))
else
(if i.val < 1836 then
(if i.val < 1835 then
![2749, 1474]
else
![580, 2750])
else
(if i.val < 1837 then
![1150, 2751]
else
(if i.val < 1838 then
![2752, 2753]
else
![2754, 214])))))
else
(if i.val < 1847 then
(if i.val < 1843 then
(if i.val < 1841 then
(if i.val < 1840 then
![2755, 2756]
else
![2757, 1548])
else
(if i.val < 1842 then
![2713, 1784]
else
![2758, 2759]))
else
(if i.val < 1845 then
(if i.val < 1844 then
![2753, 2760]
else
![2761, 1526])
else
(if i.val < 1846 then
![2762, 2763]
else
![2764, 2765])))
else
(if i.val < 1851 then
(if i.val < 1849 then
(if i.val < 1848 then
![1622, 1147]
else
![2766, 508])
else
(if i.val < 1850 then
![2767, 212]
else
![1208, 1698]))
else
(if i.val < 1853 then
(if i.val < 1852 then
![2768, 2769]
else
![2072, 2770])
else
(if i.val < 1854 then
![2771, 1533]
else
(if i.val < 1855 then
![2772, 2773]
else
![59, 2774]))))))
else
(if i.val < 1873 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
![2576, 771]
else
![2769, 716])
else
(if i.val < 1859 then
![2775, 2776]
else
![2777, 2778]))
else
(if i.val < 1862 then
(if i.val < 1861 then
![2073, 2548]
else
![2779, 2780])
else
(if i.val < 1863 then
![1235, 669]
else
![2781, 1072])))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
![1509, 1205]
else
![2735, 2593])
else
(if i.val < 1867 then
![1946, 2782]
else
![1841, 2086]))
else
(if i.val < 1870 then
(if i.val < 1869 then
![2783, 1225]
else
![2215, 2784])
else
(if i.val < 1871 then
![2075, 2785]
else
(if i.val < 1872 then
![2786, 2787]
else
![2788, 2789])))))
else
(if i.val < 1881 then
(if i.val < 1877 then
(if i.val < 1875 then
(if i.val < 1874 then
![2784, 2790]
else
![2791, 989])
else
(if i.val < 1876 then
![2792, 2793]
else
![2794, 2795]))
else
(if i.val < 1879 then
(if i.val < 1878 then
![1752, 2796]
else
![2797, 2798])
else
(if i.val < 1880 then
![500, 2527]
else
![2799, 1798])))
else
(if i.val < 1885 then
(if i.val < 1883 then
(if i.val < 1882 then
![537, 2800]
else
![2801, 2802])
else
(if i.val < 1884 then
![2803, 2804]
else
![2805, 2659]))
else
(if i.val < 1887 then
(if i.val < 1886 then
![2673, 2806]
else
![2077, 2807])
else
(if i.val < 1888 then
![2808, 1267]
else
(if i.val < 1889 then
![2582, 2809]
else
![1198, 2810])))))))))
else
(if i.val < 2025 then
(if i.val < 1957 then
(if i.val < 1923 then
(if i.val < 1906 then
(if i.val < 1898 then
(if i.val < 1894 then
(if i.val < 1892 then
(if i.val < 1891 then
![1418, 1592]
else
![2811, 2812])
else
(if i.val < 1893 then
![2813, 2814]
else
![2815, 2816]))
else
(if i.val < 1896 then
(if i.val < 1895 then
![1864, 169]
else
![999, 2817])
else
(if i.val < 1897 then
![2818, 527]
else
![2819, 569])))
else
(if i.val < 1902 then
(if i.val < 1900 then
(if i.val < 1899 then
![2820, 1341]
else
![2311, 2821])
else
(if i.val < 1901 then
![2822, 2823]
else
![2824, 2825]))
else
(if i.val < 1904 then
(if i.val < 1903 then
![2826, 1702]
else
![2827, 1736])
else
(if i.val < 1905 then
![2828, 2018]
else
![2829, 2830]))))
else
(if i.val < 1914 then
(if i.val < 1910 then
(if i.val < 1908 then
(if i.val < 1907 then
![2831, 2210]
else
![1096, 2254])
else
(if i.val < 1909 then
![2832, 571]
else
![2833, 2640]))
else
(if i.val < 1912 then
(if i.val < 1911 then
![2834, 2835]
else
![2081, 2836])
else
(if i.val < 1913 then
![2837, 2838]
else
![1125, 2839])))
else
(if i.val < 1918 then
(if i.val < 1916 then
(if i.val < 1915 then
![2232, 2840]
else
![2841, 2842])
else
(if i.val < 1917 then
![2835, 2843]
else
![2212, 2844]))
else
(if i.val < 1920 then
(if i.val < 1919 then
![154, 2845]
else
![2846, 1263])
else
(if i.val < 1921 then
![2590, 525]
else
(if i.val < 1922 then
![130, 2847]
else
![2848, 2849]))))))
else
(if i.val < 1940 then
(if i.val < 1931 then
(if i.val < 1927 then
(if i.val < 1925 then
(if i.val < 1924 then
![2598, 2850]
else
![2655, 1875])
else
(if i.val < 1926 then
![2851, 2852]
else
![2849, 2853]))
else
(if i.val < 1929 then
(if i.val < 1928 then
![2373, 1389]
else
![2477, 2854])
else
(if i.val < 1930 then
![2716, 714]
else
![2082, 485])))
else
(if i.val < 1935 then
(if i.val < 1933 then
(if i.val < 1932 then
![162, 2855]
else
![2856, 1623])
else
(if i.val < 1934 then
![1737, 2857]
else
![2858, 2859]))
else
(if i.val < 1937 then
(if i.val < 1936 then
![2860, 2861]
else
![2862, 2863])
else
(if i.val < 1938 then
![2864, 2865]
else
(if i.val < 1939 then
![2751, 2866]
else
![1336, 2867])))))
else
(if i.val < 1948 then
(if i.val < 1944 then
(if i.val < 1942 then
(if i.val < 1941 then
![2865, 2868]
else
![1045, 2531])
else
(if i.val < 1943 then
![183, 2869]
else
![2870, 2871]))
else
(if i.val < 1946 then
(if i.val < 1945 then
![387, 2872]
else
![2873, 2874])
else
(if i.val < 1947 then
![2875, 2876]
else
![2085, 2877])))
else
(if i.val < 1952 then
(if i.val < 1950 then
(if i.val < 1949 then
![2698, 2878]
else
![1380, 1538])
else
(if i.val < 1951 then
![2876, 922]
else
![2290, 2879]))
else
(if i.val < 1954 then
(if i.val < 1953 then
![2087, 2558]
else
![1716, 2880])
else
(if i.val < 1955 then
![2669, 2881]
else
(if i.val < 1956 then
![2882, 2502]
else
![911, 2883])))))))
else
(if i.val < 1991 then
(if i.val < 1974 then
(if i.val < 1965 then
(if i.val < 1961 then
(if i.val < 1959 then
(if i.val < 1958 then
![2884, 1513]
else
![393, 1685])
else
(if i.val < 1960 then
![471, 2885]
else
![2886, 2887]))
else
(if i.val < 1963 then
(if i.val < 1962 then
![582, 1877]
else
![2885, 2888])
else
(if i.val < 1964 then
![2889, 2546]
else
![1817, 449])))
else
(if i.val < 1969 then
(if i.val < 1967 then
(if i.val < 1966 then
![2089, 2890]
else
![2891, 2892])
else
(if i.val < 1968 then
![2893, 2894]
else
![2823, 2114]))
else
(if i.val < 1971 then
(if i.val < 1970 then
![947, 2895]
else
![2277, 1603])
else
(if i.val < 1972 then
![1181, 2896]
else
(if i.val < 1973 then
![2897, 1420]
else
![2648, 1475])))))
else
(if i.val < 1982 then
(if i.val < 1978 then
(if i.val < 1976 then
(if i.val < 1975 then
![2898, 2899]
else
![2900, 2901])
else
(if i.val < 1977 then
![2567, 2165]
else
![2902, 2565]))
else
(if i.val < 1980 then
(if i.val < 1979 then
![1068, 2903]
else
![2904, 2905])
else
(if i.val < 1981 then
![2906, 2907]
else
![2908, 1746])))
else
(if i.val < 1986 then
(if i.val < 1984 then
(if i.val < 1983 then
![1783, 2909]
else
![2910, 1370])
else
(if i.val < 1985 then
![2911, 2912]
else
![2445, 2913]))
else
(if i.val < 1988 then
(if i.val < 1987 then
![2914, 2915]
else
![2916, 2917])
else
(if i.val < 1989 then
![2918, 562]
else
(if i.val < 1990 then
![1107, 2919]
else
![2917, 2920]))))))
else
(if i.val < 2008 then
(if i.val < 1999 then
(if i.val < 1995 then
(if i.val < 1993 then
(if i.val < 1992 then
![2921, 1413]
else
![2922, 2923])
else
(if i.val < 1994 then
![1192, 2908]
else
![2746, 2924]))
else
(if i.val < 1997 then
(if i.val < 1996 then
![2638, 2925]
else
![2926, 2927])
else
(if i.val < 1998 then
![185, 2928]
else
![2929, 2930])))
else
(if i.val < 2003 then
(if i.val < 2001 then
(if i.val < 2000 then
![2931, 2932]
else
![2933, 302])
else
(if i.val < 2002 then
![178, 2934]
else
![2935, 2936]))
else
(if i.val < 2005 then
(if i.val < 2004 then
![1019, 2271]
else
![2937, 2938])
else
(if i.val < 2006 then
![2939, 2940]
else
(if i.val < 2007 then
![2861, 627]
else
![34, 2941])))))
else
(if i.val < 2016 then
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
![939, 2942]
else
![2943, 58])
else
(if i.val < 2011 then
![2944, 2945]
else
![988, 1330]))
else
(if i.val < 2014 then
(if i.val < 2013 then
![1200, 2946]
else
![36, 2947])
else
(if i.val < 2015 then
![2616, 2948]
else
![2949, 1635])))
else
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
![2946, 2950]
else
![931, 2951])
else
(if i.val < 2019 then
![2952, 2762]
else
![2953, 2954]))
else
(if i.val < 2022 then
(if i.val < 2021 then
![2170, 2935]
else
![457, 2955])
else
(if i.val < 2023 then
![2956, 2957]
else
(if i.val < 2024 then
![2958, 2959]
else
![1352, 2960]))))))))
else
(if i.val < 2092 then
(if i.val < 2058 then
(if i.val < 2041 then
(if i.val < 2033 then
(if i.val < 2029 then
(if i.val < 2027 then
(if i.val < 2026 then
![1577, 2961]
else
![2962, 2963])
else
(if i.val < 2028 then
![40, 2964]
else
![2620, 536]))
else
(if i.val < 2031 then
(if i.val < 2030 then
![2420, 2828]
else
![2965, 2966])
else
(if i.val < 2032 then
![555, 2967]
else
![2968, 2969])))
else
(if i.val < 2037 then
(if i.val < 2035 then
(if i.val < 2034 then
![2970, 1337]
else
![180, 2971])
else
(if i.val < 2036 then
![509, 2916]
else
![700, 1108]))
else
(if i.val < 2039 then
(if i.val < 2038 then
![2380, 573]
else
![2248, 2965])
else
(if i.val < 2040 then
![191, 2972]
else
![2973, 216]))))
else
(if i.val < 2049 then
(if i.val < 2045 then
(if i.val < 2043 then
(if i.val < 2042 then
![2780, 1831]
else
![2178, 1707])
else
(if i.val < 2044 then
![2549, 2974]
else
![2883, 1574]))
else
(if i.val < 2047 then
(if i.val < 2046 then
![2975, 2976]
else
![2977, 2978])
else
(if i.val < 2048 then
![2979, 2980]
else
![2457, 2981])))
else
(if i.val < 2053 then
(if i.val < 2051 then
(if i.val < 2050 then
![543, 845]
else
![2982, 2983])
else
(if i.val < 2052 then
![2983, 2984]
else
![2985, 608]))
else
(if i.val < 2055 then
(if i.val < 2054 then
![2312, 2986]
else
![2293, 2918])
else
(if i.val < 2056 then
![2987, 2988]
else
(if i.val < 2057 then
![2989, 2990]
else
![2991, 2992]))))))
else
(if i.val < 2075 then
(if i.val < 2066 then
(if i.val < 2062 then
(if i.val < 2060 then
(if i.val < 2059 then
![584, 2993]
else
![2479, 82])
else
(if i.val < 2061 then
![2990, 2994]
else
![1196, 2995]))
else
(if i.val < 2064 then
(if i.val < 2063 then
![2600, 642]
else
![2996, 680])
else
(if i.val < 2065 then
![1237, 1642]
else
![2997, 2998])))
else
(if i.val < 2070 then
(if i.val < 2068 then
(if i.val < 2067 then
![2430, 296]
else
![2998, 2999])
else
(if i.val < 2069 then
![1187, 3000]
else
![2658, 273]))
else
(if i.val < 2072 then
(if i.val < 2071 then
![616, 3001]
else
![3002, 3003])
else
(if i.val < 2073 then
![3004, 3005]
else
(if i.val < 2074 then
![1738, 902]
else
![1939, 3006])))))
else
(if i.val < 2083 then
(if i.val < 2079 then
(if i.val < 2077 then
(if i.val < 2076 then
![3007, 1415]
else
![3008, 694])
else
(if i.val < 2078 then
![1461, 3009]
else
![1505, 3010]))
else
(if i.val < 2081 then
(if i.val < 2080 then
![3011, 3012]
else
![711, 3013])
else
(if i.val < 2082 then
![3014, 3015]
else
![1573, 2368])))
else
(if i.val < 2087 then
(if i.val < 2085 then
(if i.val < 2084 then
![57, 3016]
else
![3017, 280])
else
(if i.val < 2086 then
![3018, 1995]
else
![664, 740]))
else
(if i.val < 2089 then
(if i.val < 2088 then
![1706, 1242]
else
![2728, 3011])
else
(if i.val < 2090 then
![3019, 3020]
else
(if i.val < 2091 then
![3021, 1921]
else
![3022, 3023])))))))
else
(if i.val < 2126 then
(if i.val < 2109 then
(if i.val < 2100 then
(if i.val < 2096 then
(if i.val < 2094 then
(if i.val < 2093 then
![2667, 3024]
else
![3025, 3026])
else
(if i.val < 2095 then
![3023, 2691]
else
![2984, 3027]))
else
(if i.val < 2098 then
(if i.val < 2097 then
![3028, 3029]
else
![436, 3030])
else
(if i.val < 2099 then
![1563, 3031]
else
![448, 3032])))
else
(if i.val < 2104 then
(if i.val < 2102 then
(if i.val < 2101 then
![2899, 2020]
else
![3031, 3033])
else
(if i.val < 2103 then
![655, 2929]
else
![2938, 3034]))
else
(if i.val < 2106 then
(if i.val < 2105 then
![3035, 1826]
else
![3036, 849])
else
(if i.val < 2107 then
![3037, 3038]
else
(if i.val < 2108 then
![3039, 3040]
else
![2980, 3041])))))
else
(if i.val < 2117 then
(if i.val < 2113 then
(if i.val < 2111 then
(if i.val < 2110 then
![3042, 3043]
else
![3044, 3045])
else
(if i.val < 2112 then
![2912, 3046]
else
![609, 3047]))
else
(if i.val < 2115 then
(if i.val < 2114 then
![1788, 3048]
else
![2622, 2732])
else
(if i.val < 2116 then
![1405, 1789]
else
![1514, 3049])))
else
(if i.val < 2121 then
(if i.val < 2119 then
(if i.val < 2118 then
![3050, 3051]
else
![2940, 2752])
else
(if i.val < 2120 then
![3052, 3053]
else
![1885, 3054]))
else
(if i.val < 2123 then
(if i.val < 2122 then
![3051, 2684]
else
![491, 3055])
else
(if i.val < 2124 then
![3056, 1629]
else
(if i.val < 2125 then
![498, 2482]
else
![3057, 322]))))))
else
(if i.val < 2143 then
(if i.val < 2134 then
(if i.val < 2130 then
(if i.val < 2128 then
(if i.val < 2127 then
![2217, 1566]
else
![3058, 3059])
else
(if i.val < 2129 then
![813, 2566]
else
![2218, 3060]))
else
(if i.val < 2132 then
(if i.val < 2131 then
![645, 2088]
else
![834, 2541])
else
(if i.val < 2133 then
![3061, 3062]
else
![517, 3063])))
else
(if i.val < 2138 then
(if i.val < 2136 then
(if i.val < 2135 then
![1880, 3064]
else
![3065, 3066])
else
(if i.val < 2137 then
![1047, 3067]
else
![2941, 2758]))
else
(if i.val < 2140 then
(if i.val < 2139 then
![3068, 3069]
else
![1546, 3070])
else
(if i.val < 2141 then
![3071, 3072]
else
(if i.val < 2142 then
![3073, 1020]
else
![628, 3074])))))
else
(if i.val < 2151 then
(if i.val < 2147 then
(if i.val < 2145 then
(if i.val < 2144 then
![2452, 1558]
else
![450, 1761])
else
(if i.val < 2146 then
![3075, 3076]
else
![1866, 31]))
else
(if i.val < 2149 then
(if i.val < 2148 then
![3077, 1966]
else
![3078, 3079])
else
(if i.val < 2150 then
![3080, 3081]
else
![3082, 869])))
else
(if i.val < 2155 then
(if i.val < 2153 then
(if i.val < 2152 then
![3076, 43]
else
![1188, 1748])
else
(if i.val < 2154 then
![1956, 2629]
else
![2896, 3083]))
else
(if i.val < 2157 then
(if i.val < 2156 then
![3084, 264]
else
![3085, 3086])
else
(if i.val < 2158 then
![195, 3087]
else
(if i.val < 2159 then
![1579, 2109]
else
![3088, 3089]))))))))))))
else
(if i.val < 3240 then
(if i.val < 2700 then
(if i.val < 2430 then
(if i.val < 2295 then
(if i.val < 2227 then
(if i.val < 2193 then
(if i.val < 2176 then
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
![515, 1662]
else
![3090, 1170])
else
(if i.val < 2163 then
![3091, 3092]
else
![3093, 282]))
else
(if i.val < 2166 then
(if i.val < 2165 then
![3066, 2631]
else
![3094, 2116])
else
(if i.val < 2167 then
![624, 3095]
else
![3096, 3097])))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
![3098, 2194]
else
![3099, 3100])
else
(if i.val < 2171 then
![74, 3101]
else
![2967, 3102]))
else
(if i.val < 2174 then
(if i.val < 2173 then
![633, 864]
else
![3103, 3104])
else
(if i.val < 2175 then
![3105, 3106]
else
![3107, 1648]))))
else
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
![454, 3108]
else
![1907, 783])
else
(if i.val < 2179 then
![3109, 1082]
else
![1143, 1434]))
else
(if i.val < 2182 then
(if i.val < 2181 then
![3067, 2973]
else
![2244, 3110])
else
(if i.val < 2183 then
![2158, 2949]
else
![1050, 3111])))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
![3112, 3113]
else
![2942, 3114])
else
(if i.val < 2187 then
![2839, 3115]
else
![3116, 3117]))
else
(if i.val < 2190 then
(if i.val < 2189 then
![3113, 3118]
else
![3119, 2118])
else
(if i.val < 2191 then
![3120, 3121]
else
(if i.val < 2192 then
![2857, 1034]
else
![3122, 3022]))))))
else
(if i.val < 2210 then
(if i.val < 2201 then
(if i.val < 2197 then
(if i.val < 2195 then
(if i.val < 2194 then
![3029, 3123]
else
![3124, 1464])
else
(if i.val < 2196 then
![3125, 3126]
else
![2945, 3127]))
else
(if i.val < 2199 then
(if i.val < 2198 then
![3128, 1991]
else
![698, 3129])
else
(if i.val < 2200 then
![1424, 3130]
else
![959, 2584])))
else
(if i.val < 2205 then
(if i.val < 2203 then
(if i.val < 2202 then
![1725, 3131]
else
![2485, 3021])
else
(if i.val < 2204 then
![1655, 3132]
else
![3010, 3133]))
else
(if i.val < 2207 then
(if i.val < 2206 then
![3134, 3135]
else
![2179, 3136])
else
(if i.val < 2208 then
![3137, 706]
else
(if i.val < 2209 then
![3138, 3139]
else
![3140, 3141])))))
else
(if i.val < 2218 then
(if i.val < 2214 then
(if i.val < 2212 then
(if i.val < 2211 then
![679, 3142]
else
![3135, 3143])
else
(if i.val < 2213 then
![3144, 3145]
else
![2993, 3146]))
else
(if i.val < 2216 then
(if i.val < 2215 then
![3147, 3148]
else
![3149, 2040])
else
(if i.val < 2217 then
![639, 2076]
else
![3150, 3151])))
else
(if i.val < 2222 then
(if i.val < 2220 then
(if i.val < 2219 then
![3151, 3152]
else
![2947, 3153])
else
(if i.val < 2221 then
![3154, 3155]
else
![1331, 3156]))
else
(if i.val < 2224 then
(if i.val < 2223 then
![3157, 3158]
else
![572, 3159])
else
(if i.val < 2225 then
![2950, 3160]
else
(if i.val < 2226 then
![2650, 3014]
else
![2948, 3161])))))))
else
(if i.val < 2261 then
(if i.val < 2244 then
(if i.val < 2235 then
(if i.val < 2231 then
(if i.val < 2229 then
(if i.val < 2228 then
![1515, 3162]
else
![1361, 3163])
else
(if i.val < 2230 then
![3164, 3165]
else
![3166, 3167]))
else
(if i.val < 2233 then
(if i.val < 2232 then
![3168, 3169]
else
![1837, 3170])
else
(if i.val < 2234 then
![3171, 3172]
else
![3173, 3174])))
else
(if i.val < 2239 then
(if i.val < 2237 then
(if i.val < 2236 then
![566, 3175]
else
![3176, 1986])
else
(if i.val < 2238 then
![3177, 1209]
else
![3178, 3179]))
else
(if i.val < 2241 then
(if i.val < 2240 then
![1204, 933]
else
![3180, 3181])
else
(if i.val < 2242 then
![3182, 3183]
else
(if i.val < 2243 then
![2981, 3184]
else
![476, 3185])))))
else
(if i.val < 2252 then
(if i.val < 2248 then
(if i.val < 2246 then
(if i.val < 2245 then
![2398, 2889]
else
![1786, 3186])
else
(if i.val < 2247 then
![3003, 390]
else
![3187, 3188]))
else
(if i.val < 2250 then
(if i.val < 2249 then
![85, 2569]
else
![3054, 306])
else
(if i.val < 2251 then
![3189, 3190]
else
![3191, 3192])))
else
(if i.val < 2256 then
(if i.val < 2254 then
(if i.val < 2253 then
![3193, 3194]
else
![3195, 127])
else
(if i.val < 2255 then
![773, 2370]
else
![3192, 3196]))
else
(if i.val < 2258 then
(if i.val < 2257 then
![3152, 3197]
else
![1683, 3198])
else
(if i.val < 2259 then
![3199, 1640]
else
(if i.val < 2260 then
![3200, 3201]
else
![482, 2028]))))))
else
(if i.val < 2278 then
(if i.val < 2269 then
(if i.val < 2265 then
(if i.val < 2263 then
(if i.val < 2262 then
![2951, 3202]
else
![3203, 3204])
else
(if i.val < 2264 then
![3205, 3206]
else
![684, 785]))
else
(if i.val < 2267 then
(if i.val < 2266 then
![1814, 3207]
else
![1497, 3208])
else
(if i.val < 2268 then
![2136, 1678]
else
![3209, 3210])))
else
(if i.val < 2273 then
(if i.val < 2271 then
(if i.val < 2270 then
![3148, 2740]
else
![3211, 3212])
else
(if i.val < 2272 then
![2992, 3213]
else
![170, 3214]))
else
(if i.val < 2275 then
(if i.val < 2274 then
![3215, 3216]
else
![1827, 924])
else
(if i.val < 2276 then
![3217, 54]
else
(if i.val < 2277 then
![2954, 278]
else
![3218, 3219])))))
else
(if i.val < 2286 then
(if i.val < 2282 then
(if i.val < 2280 then
(if i.val < 2279 then
![3220, 3221]
else
![2963, 3222])
else
(if i.val < 2281 then
![3223, 2408]
else
![607, 2083]))
else
(if i.val < 2284 then
(if i.val < 2283 then
![1985, 3224]
else
![3225, 3226])
else
(if i.val < 2285 then
![3227, 3228]
else
![3229, 3230])))
else
(if i.val < 2290 then
(if i.val < 2288 then
(if i.val < 2287 then
![3231, 3232]
else
![2955, 3233])
else
(if i.val < 2289 then
![3234, 3235]
else
![92, 3236]))
else
(if i.val < 2292 then
(if i.val < 2291 then
![1344, 2791]
else
![3232, 2624])
else
(if i.val < 2293 then
![2540, 3237]
else
(if i.val < 2294 then
![1522, 3238]
else
![1801, 2432]))))))))
else
(if i.val < 2362 then
(if i.val < 2328 then
(if i.val < 2311 then
(if i.val < 2303 then
(if i.val < 2299 then
(if i.val < 2297 then
(if i.val < 2296 then
![810, 3239]
else
![2957, 298])
else
(if i.val < 2298 then
![3240, 1144]
else
![1859, 3241]))
else
(if i.val < 2301 then
(if i.val < 2300 then
![3242, 3243]
else
![3239, 2656])
else
(if i.val < 2302 then
![3244, 3245]
else
![439, 1503])))
else
(if i.val < 2307 then
(if i.val < 2305 then
(if i.val < 2304 then
![3246, 3247]
else
![3059, 3248])
else
(if i.val < 2306 then
![2961, 3249]
else
![2867, 3250]))
else
(if i.val < 2309 then
(if i.val < 2308 then
![1692, 3164]
else
![497, 2196])
else
(if i.val < 2310 then
![715, 2266]
else
![2959, 3251]))))
else
(if i.val < 2319 then
(if i.val < 2315 then
(if i.val < 2313 then
(if i.val < 2312 then
![3252, 35]
else
![3253, 2175])
else
(if i.val < 2314 then
![3254, 3255]
else
![1507, 3256]))
else
(if i.val < 2317 then
(if i.val < 2316 then
![1869, 2226]
else
![3257, 3258])
else
(if i.val < 2318 then
![3259, 3260]
else
![2923, 1590])))
else
(if i.val < 2323 then
(if i.val < 2321 then
(if i.val < 2320 then
![3261, 914]
else
![3262, 1157])
else
(if i.val < 2322 then
![3260, 2551]
else
![3263, 114]))
else
(if i.val < 2325 then
(if i.val < 2324 then
![703, 3264]
else
![3265, 349])
else
(if i.val < 2326 then
![3266, 392]
else
(if i.val < 2327 then
![2960, 1594]
else
![3267, 1227]))))))
else
(if i.val < 2345 then
(if i.val < 2336 then
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
![3268, 1705]
else
![1481, 3269])
else
(if i.val < 2331 then
![3270, 3271]
else
![3272, 3273]))
else
(if i.val < 2334 then
(if i.val < 2333 then
![1127, 3274]
else
![3269, 3275])
else
(if i.val < 2335 then
![3276, 3277]
else
![3278, 1390])))
else
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
![1795, 3279]
else
![3032, 3280])
else
(if i.val < 2339 then
![1449, 3281]
else
![3282, 3283]))
else
(if i.val < 2342 then
(if i.val < 2341 then
![1532, 1142]
else
![3281, 3284])
else
(if i.val < 2343 then
![2852, 3285]
else
(if i.val < 2344 then
![3286, 257]
else
![3287, 3288])))))
else
(if i.val < 2353 then
(if i.val < 2349 then
(if i.val < 2347 then
(if i.val < 2346 then
![3289, 3290]
else
![3291, 1750])
else
(if i.val < 2348 then
![2722, 3292]
else
![3293, 3191]))
else
(if i.val < 2351 then
(if i.val < 2350 then
![1902, 2487]
else
![3030, 3294])
else
(if i.val < 2352 then
![3295, 252]
else
![1892, 993])))
else
(if i.val < 2357 then
(if i.val < 2355 then
(if i.val < 2354 then
![2964, 2834]
else
![2703, 3296])
else
(if i.val < 2356 then
![3297, 3298]
else
![1732, 3193]))
else
(if i.val < 2359 then
(if i.val < 2358 then
![3299, 3300]
else
![3301, 3182])
else
(if i.val < 2360 then
![1226, 3299]
else
(if i.val < 2361 then
![2731, 3302]
else
![3273, 2046])))))))
else
(if i.val < 2396 then
(if i.val < 2379 then
(if i.val < 2370 then
(if i.val < 2366 then
(if i.val < 2364 then
(if i.val < 2363 then
![1604, 1942]
else
![2621, 1619])
else
(if i.val < 2365 then
![3303, 928]
else
![1694, 3304]))
else
(if i.val < 2368 then
(if i.val < 2367 then
![3305, 3306]
else
![2098, 2268])
else
(if i.val < 2369 then
![3307, 3308]
else
![2925, 1637])))
else
(if i.val < 2374 then
(if i.val < 2372 then
(if i.val < 2371 then
![3309, 2219]
else
![1668, 3310])
else
(if i.val < 2373 then
![1677, 3311]
else
![3312, 3313]))
else
(if i.val < 2376 then
(if i.val < 2375 then
![3047, 3314]
else
![3310, 2937])
else
(if i.val < 2377 then
![3315, 1999]
else
(if i.val < 2378 then
![3316, 778]
else
![518, 3317])))))
else
(if i.val < 2387 then
(if i.val < 2383 then
(if i.val < 2381 then
(if i.val < 2380 then
![3318, 3177]
else
![3319, 3320])
else
(if i.val < 2382 then
![1410, 3321]
else
![1811, 3322]))
else
(if i.val < 2385 then
(if i.val < 2384 then
![3323, 2238]
else
![1565, 892])
else
(if i.val < 2386 then
![3258, 1265]
else
![3320, 3324])))
else
(if i.val < 2391 then
(if i.val < 2389 then
(if i.val < 2388 then
![3083, 3325]
else
![3326, 3327])
else
(if i.val < 2390 then
![3328, 3329]
else
![3045, 3330]))
else
(if i.val < 2393 then
(if i.val < 2392 then
![1994, 3331]
else
![2966, 3332])
else
(if i.val < 2394 then
![1983, 3333]
else
(if i.val < 2395 then
![3334, 3335]
else
![341, 3336]))))))
else
(if i.val < 2413 then
(if i.val < 2404 then
(if i.val < 2400 then
(if i.val < 2398 then
(if i.val < 2397 then
![3331, 2294]
else
![2836, 3042])
else
(if i.val < 2399 then
![1230, 1695]
else
![2237, 3337]))
else
(if i.val < 2402 then
(if i.val < 2401 then
![1720, 3134]
else
![3338, 3339])
else
(if i.val < 2403 then
![2969, 3340]
else
![992, 1860])))
else
(if i.val < 2408 then
(if i.val < 2406 then
(if i.val < 2405 then
![1615, 1791]
else
![3341, 377])
else
(if i.val < 2407 then
![3342, 2048]
else
![3339, 2607]))
else
(if i.val < 2410 then
(if i.val < 2409 then
![3343, 3344]
else
![3345, 997])
else
(if i.val < 2411 then
![3346, 3347]
else
(if i.val < 2412 then
![2225, 3348]
else
![3349, 3350])))))
else
(if i.val < 2421 then
(if i.val < 2417 then
(if i.val < 2415 then
(if i.val < 2414 then
![3351, 365]
else
![3352, 3353])
else
(if i.val < 2416 then
![1453, 3354]
else
![3355, 3356]))
else
(if i.val < 2419 then
(if i.val < 2418 then
![2971, 3357]
else
![3358, 3359])
else
(if i.val < 2420 then
![3360, 3361]
else
![652, 2687])))
else
(if i.val < 2425 then
(if i.val < 2423 then
(if i.val < 2422 then
![3356, 3028]
else
![3362, 3363])
else
(if i.val < 2424 then
![1785, 2258]
else
![1527, 718]))
else
(if i.val < 2427 then
(if i.val < 2426 then
![3364, 3365]
else
![1876, 3366])
else
(if i.val < 2428 then
![3250, 3367]
else
(if i.val < 2429 then
![3368, 3369]
else
![1943, 2276])))))))))
else
(if i.val < 2565 then
(if i.val < 2497 then
(if i.val < 2463 then
(if i.val < 2446 then
(if i.val < 2438 then
(if i.val < 2434 then
(if i.val < 2432 then
(if i.val < 2431 then
![1081, 3370]
else
![3370, 3371])
else
(if i.val < 2433 then
![2665, 3372]
else
![3038, 3373]))
else
(if i.val < 2436 then
(if i.val < 2435 then
![3374, 101]
else
![3129, 3375])
else
(if i.val < 2437 then
![3376, 320]
else
![3377, 3378])))
else
(if i.val < 2442 then
(if i.val < 2440 then
(if i.val < 2439 then
![249, 964]
else
![621, 3098])
else
(if i.val < 2441 then
![535, 2279]
else
![3194, 1110]))
else
(if i.val < 2444 then
(if i.val < 2443 then
![1442, 1971]
else
![2843, 39])
else
(if i.val < 2445 then
![1484, 3379]
else
![323, 3380]))))
else
(if i.val < 2454 then
(if i.val < 2450 then
(if i.val < 2448 then
(if i.val < 2447 then
![3381, 2166]
else
![1606, 3382])
else
(if i.val < 2449 then
![3383, 3384]
else
![3385, 313]))
else
(if i.val < 2452 then
(if i.val < 2451 then
![3386, 2846]
else
![3384, 3387])
else
(if i.val < 2453 then
![1959, 3388]
else
![3389, 814])))
else
(if i.val < 2458 then
(if i.val < 2456 then
(if i.val < 2455 then
![3390, 311]
else
![3391, 3392])
else
(if i.val < 2457 then
![3393, 3394]
else
![89, 2597]))
else
(if i.val < 2460 then
(if i.val < 2459 then
![3275, 1280]
else
![3392, 1012])
else
(if i.val < 2461 then
![1927, 3254]
else
(if i.val < 2462 then
![3395, 3396]
else
![1679, 966]))))))
else
(if i.val < 2480 then
(if i.val < 2471 then
(if i.val < 2467 then
(if i.val < 2465 then
(if i.val < 2464 then
![1933, 1654]
else
![3371, 3286])
else
(if i.val < 2466 then
![2528, 3397]
else
![594, 1829]))
else
(if i.val < 2469 then
(if i.val < 2468 then
![2928, 1669]
else
![2800, 3398])
else
(if i.val < 2470 then
![1106, 3399]
else
![3400, 1739])))
else
(if i.val < 2475 then
(if i.val < 2473 then
(if i.val < 2472 then
![1964, 3401]
else
![3398, 2619])
else
(if i.val < 2474 then
![2744, 1466]
else
![1704, 3402]))
else
(if i.val < 2477 then
(if i.val < 2476 then
![1920, 3403]
else
![2386, 1024])
else
(if i.val < 2478 then
![1893, 3404]
else
(if i.val < 2479 then
![3405, 394]
else
![842, 3406])))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
![1871, 3407]
else
![1769, 1899])
else
(if i.val < 2483 then
![2972, 3408]
else
![3409, 2015]))
else
(if i.val < 2486 then
(if i.val < 2485 then
![3280, 3410]
else
![1649, 3411])
else
(if i.val < 2487 then
![2125, 2252]
else
![3412, 1952])))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
![1779, 3413]
else
![3414, 3415])
else
(if i.val < 2491 then
![2463, 270]
else
![1476, 3416]))
else
(if i.val < 2494 then
(if i.val < 2493 then
![693, 832]
else
![3417, 873])
else
(if i.val < 2495 then
![3100, 3418]
else
(if i.val < 2496 then
![3419, 1195]
else
![1754, 3420])))))))
else
(if i.val < 2531 then
(if i.val < 2514 then
(if i.val < 2505 then
(if i.val < 2501 then
(if i.val < 2499 then
(if i.val < 2498 then
![3421, 2343]
else
![1772, 3422])
else
(if i.val < 2500 then
![3423, 875]
else
![3424, 3315]))
else
(if i.val < 2503 then
(if i.val < 2502 then
![3425, 3426]
else
![1583, 3427])
else
(if i.val < 2504 then
![3428, 3429]
else
![3426, 3430])))
else
(if i.val < 2509 then
(if i.val < 2507 then
(if i.val < 2506 then
![3046, 3431]
else
![255, 1022])
else
(if i.val < 2508 then
![3432, 2011]
else
![3285, 830]))
else
(if i.val < 2511 then
(if i.val < 2510 then
![3288, 3433]
else
![3327, 2474])
else
(if i.val < 2512 then
![3434, 3435]
else
(if i.val < 2513 then
![376, 3436]
else
![3133, 2106])))))
else
(if i.val < 2522 then
(if i.val < 2518 then
(if i.val < 2516 then
(if i.val < 2515 then
![3206, 3437]
else
![717, 1010])
else
(if i.val < 2517 then
![2974, 795]
else
![263, 3438]))
else
(if i.val < 2520 then
(if i.val < 2519 then
![3439, 2278]
else
![2372, 3440])
else
(if i.val < 2521 then
![3441, 103]
else
![3442, 3443])))
else
(if i.val < 2526 then
(if i.val < 2524 then
(if i.val < 2523 then
![3382, 3444]
else
![3443, 3445])
else
(if i.val < 2525 then
![284, 3446]
else
![3447, 2803]))
else
(if i.val < 2528 then
(if i.val < 2527 then
![564, 2792]
else
![3448, 3449])
else
(if i.val < 2529 then
![3450, 3451]
else
(if i.val < 2530 then
![2976, 3452]
else
![3354, 2882]))))))
else
(if i.val < 2548 then
(if i.val < 2539 then
(if i.val < 2535 then
(if i.val < 2533 then
(if i.val < 2532 then
![2097, 2213]
else
![3451, 640])
else
(if i.val < 2534 then
![1830, 3262]
else
![2354, 3453]))
else
(if i.val < 2537 then
(if i.val < 2536 then
![3454, 3223]
else
![1398, 3455])
else
(if i.val < 2538 then
![3456, 1936]
else
![570, 2330])))
else
(if i.val < 2543 then
(if i.val < 2541 then
(if i.val < 2540 then
![886, 2476]
else
![369, 3457])
else
(if i.val < 2542 then
![3458, 3252]
else
![2431, 763]))
else
(if i.val < 2545 then
(if i.val < 2544 then
![2978, 3459]
else
![1884, 3460])
else
(if i.val < 2546 then
![1430, 3461]
else
(if i.val < 2547 then
![3081, 2261]
else
![1996, 2167])))))
else
(if i.val < 2556 then
(if i.val < 2552 then
(if i.val < 2550 then
(if i.val < 2549 then
![3462, 1180]
else
![3463, 3464])
else
(if i.val < 2551 then
![3465, 3267]
else
![1541, 3466]))
else
(if i.val < 2554 then
(if i.val < 2553 then
![3467, 3468]
else
![3469, 2617])
else
(if i.val < 2555 then
![3470, 2381]
else
![2412, 3471])))
else
(if i.val < 2560 then
(if i.val < 2558 then
(if i.val < 2557 then
![1806, 3472]
else
![2920, 2766])
else
(if i.val < 2559 then
![3473, 866]
else
![1569, 3474]))
else
(if i.val < 2562 then
(if i.val < 2561 then
![1912, 2122]
else
![1643, 3470])
else
(if i.val < 2563 then
![3379, 3475]
else
(if i.val < 2564 then
![3313, 3476]
else
![3477, 3478]))))))))
else
(if i.val < 2632 then
(if i.val < 2598 then
(if i.val < 2581 then
(if i.val < 2573 then
(if i.val < 2569 then
(if i.val < 2567 then
(if i.val < 2566 then
![1922, 3479]
else
![3153, 3458])
else
(if i.val < 2568 then
![2774, 3480]
else
![682, 3481]))
else
(if i.val < 2571 then
(if i.val < 2570 then
![3482, 3483]
else
![585, 3484])
else
(if i.val < 2572 then
![3485, 2061]
else
![3184, 3486])))
else
(if i.val < 2577 then
(if i.val < 2575 then
(if i.val < 2574 then
![3487, 3289]
else
![3488, 3489])
else
(if i.val < 2576 then
![2888, 110]
else
![3486, 3490]))
else
(if i.val < 2579 then
(if i.val < 2578 then
![3197, 3096]
else
![3491, 3189])
else
(if i.val < 2580 then
![3034, 1667]
else
![3492, 1993]))))
else
(if i.val < 2589 then
(if i.val < 2585 then
(if i.val < 2583 then
(if i.val < 2582 then
![3459, 3493]
else
![3009, 960])
else
(if i.val < 2584 then
![3493, 942]
else
![2986, 3075]))
else
(if i.val < 2587 then
(if i.val < 2586 then
![3332, 3494]
else
![2201, 3495])
else
(if i.val < 2588 then
![3496, 496]
else
![3497, 1805])))
else
(if i.val < 2593 then
(if i.val < 2591 then
(if i.val < 2590 then
![3498, 3244]
else
![1834, 3499])
else
(if i.val < 2592 then
![3500, 3263]
else
![1844, 3501]))
else
(if i.val < 2595 then
(if i.val < 2594 then
![1874, 3502]
else
![3117, 3503])
else
(if i.val < 2596 then
![3499, 2434]
else
(if i.val < 2597 then
![3504, 3505]
else
![3506, 3334]))))))
else
(if i.val < 2615 then
(if i.val < 2606 then
(if i.val < 2602 then
(if i.val < 2600 then
(if i.val < 2599 then
![592, 3507]
else
![3508, 3509])
else
(if i.val < 2601 then
![1937, 2811]
else
![2291, 3140]))
else
(if i.val < 2604 then
(if i.val < 2603 then
![3247, 3510]
else
![3373, 370])
else
(if i.val < 2605 then
![3511, 799]
else
![1727, 766])))
else
(if i.val < 2610 then
(if i.val < 2608 then
(if i.val < 2607 then
![3512, 3513]
else
![681, 3467])
else
(if i.val < 2609 then
![3175, 3514]
else
![3027, 3515]))
else
(if i.val < 2612 then
(if i.val < 2611 then
![2869, 3516]
else
![3517, 3518])
else
(if i.val < 2613 then
![1909, 3519]
else
(if i.val < 2614 then
![3520, 1423]
else
![493, 3521])))))
else
(if i.val < 2623 then
(if i.val < 2619 then
(if i.val < 2617 then
(if i.val < 2616 then
![605, 2103]
else
![3522, 2069])
else
(if i.val < 2618 then
![1883, 3234]
else
![2988, 3523]))
else
(if i.val < 2621 then
(if i.val < 2620 then
![647, 3176]
else
![3524, 1981])
else
(if i.val < 2622 then
![653, 2891]
else
![3525, 3526])))
else
(if i.val < 2627 then
(if i.val < 2625 then
(if i.val < 2624 then
![1701, 3215]
else
![3132, 1925])
else
(if i.val < 2626 then
![672, 3527]
else
![3403, 2337]))
else
(if i.val < 2629 then
(if i.val < 2628 then
![3528, 2436]
else
![3479, 2484])
else
(if i.val < 2630 then
![2556, 3529]
else
(if i.val < 2631 then
![3530, 3303]
else
![1905, 3328])))))))
else
(if i.val < 2666 then
(if i.val < 2649 then
(if i.val < 2640 then
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
![3531, 3381]
else
![2994, 3532])
else
(if i.val < 2635 then
![3533, 3534]
else
![2878, 1913]))
else
(if i.val < 2638 then
(if i.val < 2637 then
![3535, 2943]
else
![3536, 3323])
else
(if i.val < 2639 then
![3401, 411]
else
![3537, 1128])))
else
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
![1774, 3538]
else
![3539, 3540])
else
(if i.val < 2643 then
![1557, 3541]
else
![3542, 860]))
else
(if i.val < 2646 then
(if i.val < 2645 then
![3172, 9]
else
![3543, 3544])
else
(if i.val < 2647 then
![3540, 1496]
else
(if i.val < 2648 then
![1487, 3391]
else
![3545, 3546])))))
else
(if i.val < 2657 then
(if i.val < 2653 then
(if i.val < 2651 then
(if i.val < 2650 then
![3060, 3547]
else
![1961, 3548])
else
(if i.val < 2652 then
![3549, 372]
else
![2437, 1771]))
else
(if i.val < 2655 then
(if i.val < 2654 then
![666, 352]
else
![1821, 287])
else
(if i.val < 2656 then
![3550, 3551]
else
![3552, 938])))
else
(if i.val < 2661 then
(if i.val < 2659 then
(if i.val < 2658 then
![3416, 839]
else
![102, 2235])
else
(if i.val < 2660 then
![3013, 3553]
else
![3551, 1126]))
else
(if i.val < 2663 then
(if i.val < 2662 then
![3554, 2044]
else
![3555, 3556])
else
(if i.val < 2664 then
![3201, 1997]
else
(if i.val < 2665 then
![612, 2404]
else
![1638, 3557]))))))
else
(if i.val < 2683 then
(if i.val < 2674 then
(if i.val < 2670 then
(if i.val < 2668 then
(if i.val < 2667 then
![3330, 455]
else
![920, 1715])
else
(if i.val < 2669 then
![2750, 3558]
else
![2367, 3559]))
else
(if i.val < 2672 then
(if i.val < 2671 then
![3560, 3342]
else
![2907, 1836])
else
(if i.val < 2673 then
![2995, 3166]
else
![3561, 3562])))
else
(if i.val < 2678 then
(if i.val < 2676 then
(if i.val < 2675 then
![3431, 3563]
else
![3256, 3564])
else
(if i.val < 2677 then
![3314, 3565]
else
![213, 3393]))
else
(if i.val < 2680 then
(if i.val < 2679 then
![1343, 1974]
else
![3363, 3217])
else
(if i.val < 2681 then
![3350, 3566]
else
(if i.val < 2682 then
![3567, 2618]
else
![3188, 3568])))))
else
(if i.val < 2691 then
(if i.val < 2687 then
(if i.val < 2685 then
(if i.val < 2684 then
![2100, 2904]
else
![2448, 3569])
else
(if i.val < 2686 then
![3570, 3571]
else
![3228, 3572]))
else
(if i.val < 2689 then
(if i.val < 2688 then
![1422, 3573]
else
![2901, 3574])
else
(if i.val < 2690 then
![1523, 3575]
else
![1212, 3576])))
else
(if i.val < 2695 then
(if i.val < 2693 then
(if i.val < 2692 then
![1599, 2137]
else
![3577, 3266])
else
(if i.val < 2694 then
![2894, 2033]
else
![3502, 953]))
else
(if i.val < 2697 then
(if i.val < 2696 then
![3578, 3579]
else
![3174, 3580])
else
(if i.val < 2698 then
![3581, 3582]
else
(if i.val < 2699 then
![3583, 2939]
else
![3584, 149]))))))))))
else
(if i.val < 2970 then
(if i.val < 2835 then
(if i.val < 2767 then
(if i.val < 2733 then
(if i.val < 2716 then
(if i.val < 2708 then
(if i.val < 2704 then
(if i.val < 2702 then
(if i.val < 2701 then
![3579, 3585]
else
![3294, 3586])
else
(if i.val < 2703 then
![3489, 405]
else
![3587, 3588]))
else
(if i.val < 2706 then
(if i.val < 2705 then
![3063, 3589]
else
![3590, 2090])
else
(if i.val < 2707 then
![2001, 2591]
else
![451, 3112])))
else
(if i.val < 2712 then
(if i.val < 2710 then
(if i.val < 2709 then
![3070, 3591]
else
![3298, 3358])
else
(if i.val < 2711 then
![2999, 3592]
else
![3593, 3504]))
else
(if i.val < 2714 then
(if i.val < 2713 then
![105, 2668]
else
![3594, 3595])
else
(if i.val < 2715 then
![453, 3293]
else
![1747, 2119]))))
else
(if i.val < 2724 then
(if i.val < 2720 then
(if i.val < 2718 then
(if i.val < 2717 then
![3361, 140]
else
![3097, 3150])
else
(if i.val < 2719 then
![3595, 1008]
else
![3429, 1124]))
else
(if i.val < 2722 then
(if i.val < 2721 then
![3596, 413]
else
![3597, 2438])
else
(if i.val < 2723 then
![2592, 547]
else
![3598, 3599])))
else
(if i.val < 2728 then
(if i.val < 2726 then
(if i.val < 2725 then
![1589, 3600]
else
![3163, 935])
else
(if i.val < 2727 then
![3538, 2537]
else
![3121, 3601]))
else
(if i.val < 2730 then
(if i.val < 2729 then
![113, 3602]
else
![3216, 398])
else
(if i.val < 2731 then
![3603, 2157]
else
(if i.val < 2732 then
![945, 3604]
else
![3605, 3606]))))))
else
(if i.val < 2750 then
(if i.val < 2741 then
(if i.val < 2737 then
(if i.val < 2735 then
(if i.val < 2734 then
![870, 2813]
else
![3604, 2557])
else
(if i.val < 2736 then
![3114, 3607]
else
![3516, 3608]))
else
(if i.val < 2739 then
(if i.val < 2738 then
![3609, 3610]
else
![3611, 3318])
else
(if i.val < 2740 then
![3413, 3612]
else
![3000, 3065])))
else
(if i.val < 2745 then
(if i.val < 2743 then
(if i.val < 2742 then
![3613, 2111]
else
![3614, 955])
else
(if i.val < 2744 then
![1953, 1048]
else
![3612, 3615]))
else
(if i.val < 2747 then
(if i.val < 2746 then
![3588, 3616]
else
![3617, 129])
else
(if i.val < 2748 then
![3510, 1175]
else
(if i.val < 2749 then
![3476, 2289]
else
![1713, 3618])))))
else
(if i.val < 2758 then
(if i.val < 2754 then
(if i.val < 2752 then
(if i.val < 2751 then
![2610, 2344]
else
![3041, 2833])
else
(if i.val < 2753 then
![3322, 2601]
else
![2306, 2509]))
else
(if i.val < 2756 then
(if i.val < 2755 then
![3126, 3619]
else
![3620, 3621])
else
(if i.val < 2757 then
![2155, 3622]
else
![3001, 3623])))
else
(if i.val < 2762 then
(if i.val < 2760 then
(if i.val < 2759 then
![2328, 3624]
else
![1730, 3625])
else
(if i.val < 2761 then
![3622, 3626]
else
![2180, 3627]))
else
(if i.val < 2764 then
(if i.val < 2763 then
![290, 2858]
else
![1075, 2494])
else
(if i.val < 2765 then
![269, 2332]
else
(if i.val < 2766 then
![2260, 3628]
else
![597, 1872])))))))
else
(if i.val < 2801 then
(if i.val < 2784 then
(if i.val < 2775 then
(if i.val < 2771 then
(if i.val < 2769 then
(if i.val < 2768 then
![3159, 3629]
else
![2183, 3630])
else
(if i.val < 2770 then
![3006, 2323]
else
![3131, 300]))
else
(if i.val < 2773 then
(if i.val < 2772 then
![244, 962]
else
![3005, 3631])
else
(if i.val < 2774 then
![3118, 50]
else
![3632, 2663])))
else
(if i.val < 2779 then
(if i.val < 2777 then
(if i.val < 2776 then
![1878, 3633]
else
![3079, 2714])
else
(if i.val < 2778 then
![3634, 1000]
else
![2123, 2348]))
else
(if i.val < 2781 then
(if i.val < 2780 then
![3635, 134]
else
![3636, 2654])
else
(if i.val < 2782 then
![3284, 2749]
else
(if i.val < 2783 then
![1858, 3637]
else
![2718, 3638])))))
else
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
![3637, 980]
else
![3639, 3640])
else
(if i.val < 2787 then
![3641, 1781]
else
![1539, 3642]))
else
(if i.val < 2790 then
(if i.val < 2789 then
![3643, 266]
else
![1896, 2147])
else
(if i.val < 2791 then
![2105, 2427]
else
![3644, 3082])))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
![2934, 3149]
else
![3237, 3645])
else
(if i.val < 2795 then
![3212, 347]
else
![3646, 946]))
else
(if i.val < 2798 then
(if i.val < 2797 then
![769, 3647]
else
![3087, 3648])
else
(if i.val < 2799 then
![3649, 2318]
else
(if i.val < 2800 then
![3521, 3650]
else
![2596, 2953]))))))
else
(if i.val < 2818 then
(if i.val < 2809 then
(if i.val < 2805 then
(if i.val < 2803 then
(if i.val < 2802 then
![2455, 3362]
else
![3651, 3652])
else
(if i.val < 2804 then
![3653, 3654]
else
![2652, 3605]))
else
(if i.val < 2807 then
(if i.val < 2806 then
![3321, 3655]
else
![1664, 3305])
else
(if i.val < 2808 then
![1960, 3656]
else
![3657, 1973])))
else
(if i.val < 2813 then
(if i.val < 2811 then
(if i.val < 2810 then
![3658, 2505]
else
![3659, 3660])
else
(if i.val < 2812 then
![3661, 3662]
else
![1365, 1988]))
else
(if i.val < 2815 then
(if i.val < 2814 then
![3204, 2707]
else
![1512, 37])
else
(if i.val < 2816 then
![3663, 3539]
else
(if i.val < 2817 then
![1608, 3664]
else
![673, 3665])))))
else
(if i.val < 2826 then
(if i.val < 2822 then
(if i.val < 2820 then
(if i.val < 2819 then
![3666, 3597]
else
![1929, 1149])
else
(if i.val < 2821 then
![3541, 3259]
else
![3378, 3667]))
else
(if i.val < 2824 then
(if i.val < 2823 then
![3219, 3668]
else
![798, 2952])
else
(if i.val < 2825 then
![3012, 3669]
else
![3618, 2387])))
else
(if i.val < 2830 then
(if i.val < 2828 then
(if i.val < 2827 then
![1634, 407]
else
![100, 3670])
else
(if i.val < 2829 then
![3671, 3672]
else
![2721, 3673]))
else
(if i.val < 2832 then
(if i.val < 2831 then
![3407, 3578]
else
![1367, 3674])
else
(if i.val < 2833 then
![1969, 3675]
else
(if i.val < 2834 then
![3676, 3390]
else
![3446, 3677]))))))))
else
(if i.val < 2902 then
(if i.val < 2868 then
(if i.val < 2851 then
(if i.val < 2843 then
(if i.val < 2839 then
(if i.val < 2837 then
(if i.val < 2836 then
![2711, 3678]
else
![3679, 3680])
else
(if i.val < 2838 then
![3214, 1856]
else
![3375, 3681]))
else
(if i.val < 2841 then
(if i.val < 2840 then
![3682, 2107]
else
![3683, 3684])
else
(if i.val < 2842 then
![3015, 3685]
else
![3686, 3687])))
else
(if i.val < 2847 then
(if i.val < 2845 then
(if i.val < 2844 then
![3684, 3520]
else
![1977, 3635])
else
(if i.val < 2846 then
![3580, 3688]
else
![591, 3689]))
else
(if i.val < 2849 then
(if i.val < 2848 then
![3690, 957]
else
![3404, 1118])
else
(if i.val < 2850 then
![3688, 2384]
else
![3629, 3691]))))
else
(if i.val < 2859 then
(if i.val < 2855 then
(if i.val < 2853 then
(if i.val < 2852 then
![3514, 3439]
else
![1077, 3692])
else
(if i.val < 2854 then
![721, 3693]
else
![3694, 2223]))
else
(if i.val < 2857 then
(if i.val < 2856 then
![3435, 3695]
else
![3696, 440])
else
(if i.val < 2858 then
![2497, 3211]
else
![3016, 3697])))
else
(if i.val < 2863 then
(if i.val < 2861 then
(if i.val < 2860 then
![1602, 3698]
else
![3699, 3253])
else
(if i.val < 2862 then
![3574, 2287]
else
![3700, 3425]))
else
(if i.val < 2865 then
(if i.val < 2864 then
![3359, 3701]
else
![339, 1217])
else
(if i.val < 2866 then
![2369, 3702]
else
(if i.val < 2867 then
![3606, 3703]
else
![3704, 3705]))))))
else
(if i.val < 2885 then
(if i.val < 2876 then
(if i.val < 2872 then
(if i.val < 2870 then
(if i.val < 2869 then
![3703, 2645]
else
![1141, 2422])
else
(if i.val < 2871 then
![846, 3706]
else
![3707, 3708]))
else
(if i.val < 2874 then
(if i.val < 2873 then
![3709, 2394]
else
![3710, 2709])
else
(if i.val < 2875 then
![929, 2837]
else
![3711, 948])))
else
(if i.val < 2880 then
(if i.val < 2878 then
(if i.val < 2877 then
![3708, 3712]
else
![3713, 2693])
else
(if i.val < 2879 then
![3714, 2177]
else
![3715, 982]))
else
(if i.val < 2882 then
(if i.val < 2881 then
![3716, 1329]
else
![2930, 1675])
else
(if i.val < 2883 then
![2874, 3025]
else
(if i.val < 2884 then
![87, 3717]
else
![526, 3220])))))
else
(if i.val < 2893 then
(if i.val < 2889 then
(if i.val < 2887 then
(if i.val < 2886 then
![3717, 3718]
else
![3274, 3195])
else
(if i.val < 2888 then
![3466, 3719]
else
![1105, 3720]))
else
(if i.val < 2891 then
(if i.val < 2890 then
![3721, 3722]
else
![3674, 3723])
else
(if i.val < 2892 then
![3020, 3724]
else
![1467, 2066])))
else
(if i.val < 2897 then
(if i.val < 2895 then
(if i.val < 2894 then
![2104, 3725]
else
![1998, 1386])
else
(if i.val < 2896 then
![3420, 3726]
else
![770, 360]))
else
(if i.val < 2899 then
(if i.val < 2898 then
![1853, 3727]
else
![3728, 2350])
else
(if i.val < 2900 then
![3729, 2794]
else
(if i.val < 2901 then
![294, 2815]
else
![2241, 2991])))))))
else
(if i.val < 2936 then
(if i.val < 2919 then
(if i.val < 2910 then
(if i.val < 2906 then
(if i.val < 2904 then
(if i.val < 2903 then
![3156, 2359]
else
![3415, 1134])
else
(if i.val < 2905 then
![3024, 3730]
else
![3731, 3732]))
else
(if i.val < 2908 then
(if i.val < 2907 then
![1948, 2242]
else
![3444, 2514])
else
(if i.val < 2909 then
![3733, 3734]
else
![3387, 3735])))
else
(if i.val < 2914 then
(if i.val < 2912 then
(if i.val < 2911 then
![3251, 3736]
else
![1465, 2064])
else
(if i.val < 2913 then
![1651, 1097]
else
![2362, 3737]))
else
(if i.val < 2916 then
(if i.val < 2915 then
![3648, 3463]
else
![2132, 2886])
else
(if i.val < 2917 then
![3738, 3739]
else
(if i.val < 2918 then
![3737, 481]
else
![952, 1058])))))
else
(if i.val < 2927 then
(if i.val < 2923 then
(if i.val < 2921 then
(if i.val < 2920 then
![3740, 442]
else
![2816, 3741])
else
(if i.val < 2922 then
![3742, 3231]
else
![3190, 3743]))
else
(if i.val < 2925 then
(if i.val < 2924 then
![848, 1345]
else
![3706, 3744])
else
(if i.val < 2926 then
![2498, 3745]
else
![374, 3746])))
else
(if i.val < 2931 then
(if i.val < 2929 then
(if i.val < 2928 then
![2356, 3747]
else
![720, 3748])
else
(if i.val < 2930 then
![3749, 3750]
else
![3751, 1347]))
else
(if i.val < 2933 then
(if i.val < 2932 then
![1620, 2272]
else
![3170, 3752])
else
(if i.val < 2934 then
![2614, 2702]
else
(if i.val < 2935 then
![3544, 3753]
else
![3026, 2346]))))))
else
(if i.val < 2953 then
(if i.val < 2944 then
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
![2802, 3754]
else
![3755, 88])
else
(if i.val < 2939 then
![1898, 3756]
else
![66, 3525]))
else
(if i.val < 2942 then
(if i.val < 2941 then
![3300, 3757]
else
![1416, 3758])
else
(if i.val < 2943 then
![3759, 3545]
else
![70, 3700])))
else
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
![3302, 841]
else
![3169, 1207])
else
(if i.val < 2947 then
![859, 3760]
else
![3761, 2613]))
else
(if i.val < 2950 then
(if i.val < 2949 then
![281, 3762]
else
![815, 1067])
else
(if i.val < 2951 then
![996, 1570]
else
(if i.val < 2952 then
![3139, 877]
else
![3062, 1949])))))
else
(if i.val < 2961 then
(if i.val < 2957 then
(if i.val < 2955 then
(if i.val < 2954 then
![3763, 315]
else
![3396, 2444])
else
(if i.val < 2956 then
![3255, 174]
else
![3455, 1060]))
else
(if i.val < 2959 then
(if i.val < 2958 then
![3592, 3764]
else
![1846, 2580])
else
(if i.val < 2960 then
![2000, 3765]
else
![3766, 3767])))
else
(if i.val < 2965 then
(if i.val < 2963 then
(if i.val < 2962 then
![3767, 3768]
else
![3769, 912])
else
(if i.val < 2964 then
![3101, 3770]
else
![3089, 3473]))
else
(if i.val < 2967 then
(if i.val < 2966 then
![888, 1065]
else
![3207, 138])
else
(if i.val < 2968 then
![3672, 3771]
else
(if i.val < 2969 then
![1647, 2672]
else
![3290, 940])))))))))
else
(if i.val < 3105 then
(if i.val < 3037 then
(if i.val < 3003 then
(if i.val < 2986 then
(if i.val < 2978 then
(if i.val < 2974 then
(if i.val < 2972 then
(if i.val < 2971 then
![1918, 977]
else
![3772, 1210])
else
(if i.val < 2973 then
![2159, 3773]
else
![1931, 3774]))
else
(if i.val < 2976 then
(if i.val < 2975 then
![2239, 2747]
else
![3734, 461])
else
(if i.val < 2977 then
![3775, 2563]
else
![3366, 3636])))
else
(if i.val < 2982 then
(if i.val < 2980 then
(if i.val < 2979 then
![3776, 2805]
else
![3777, 203])
else
(if i.val < 2981 then
![3750, 3778]
else
![3336, 3779]))
else
(if i.val < 2984 then
(if i.val < 2983 then
![3780, 2848]
else
![3778, 3349])
else
(if i.val < 2985 then
![3768, 3679]
else
![3781, 3782]))))
else
(if i.val < 2994 then
(if i.val < 2990 then
(if i.val < 2988 then
(if i.val < 2987 then
![2233, 1182]
else
![94, 3783])
else
(if i.val < 2989 then
![3655, 2439]
else
![3784, 2757]))
else
(if i.val < 2992 then
(if i.val < 2991 then
![3765, 3785]
else
![3786, 3714])
else
(if i.val < 2993 then
![3787, 3788]
else
![913, 3789])))
else
(if i.val < 2998 then
(if i.val < 2996 then
(if i.val < 2995 then
![2416, 3790]
else
![2115, 2417])
else
(if i.val < 2997 then
![98, 3383]
else
![2481, 3791]))
else
(if i.val < 3000 then
(if i.val < 2999 then
![1121, 3343]
else
![806, 1934])
else
(if i.val < 3001 then
![3582, 503]
else
(if i.val < 3002 then
![1318, 3268]
else
![3048, 2725]))))))
else
(if i.val < 3020 then
(if i.val < 3011 then
(if i.val < 3007 then
(if i.val < 3005 then
(if i.val < 3004 then
![943, 2977]
else
![823, 3792])
else
(if i.val < 3006 then
![2478, 3793]
else
![1520, 3794]))
else
(if i.val < 3009 then
(if i.val < 3008 then
![2220, 1166]
else
![3186, 2228])
else
(if i.val < 3010 then
![3795, 3796]
else
![2465, 61])))
else
(if i.val < 3015 then
(if i.val < 3013 then
(if i.val < 3012 then
![1145, 3797]
else
![3615, 188])
else
(if i.val < 3014 then
![3796, 73]
else
![1639, 2382]))
else
(if i.val < 3017 then
(if i.val < 3016 then
![2536, 3307]
else
![1989, 3798])
else
(if i.val < 3018 then
![3668, 613]
else
(if i.val < 3019 then
![3799, 463]
else
![3800, 1239])))))
else
(if i.val < 3028 then
(if i.val < 3024 then
(if i.val < 3022 then
(if i.val < 3021 then
![2647, 3035]
else
![2677, 3801])
else
(if i.val < 3023 then
![3760, 3802]
else
![932, 1362]))
else
(if i.val < 3026 then
(if i.val < 3025 then
![3803, 3804]
else
![1214, 1291])
else
(if i.val < 3027 then
![2798, 1554]
else
![3794, 3763])))
else
(if i.val < 3032 then
(if i.val < 3030 then
(if i.val < 3029 then
![3573, 3805]
else
![3427, 3806])
else
(if i.val < 3031 then
![3807, 2824]
else
![3576, 3808]))
else
(if i.val < 3034 then
(if i.val < 3033 then
![3809, 2996]
else
![3440, 1508])
else
(if i.val < 3035 then
![3782, 3707]
else
(if i.val < 3036 then
![3810, 2162]
else
![3811, 3812])))))))
else
(if i.val < 3071 then
(if i.val < 3054 then
(if i.val < 3045 then
(if i.val < 3041 then
(if i.val < 3039 then
(if i.val < 3038 then
![3756, 3709]
else
![3556, 2560])
else
(if i.val < 3040 then
![994, 2594]
else
![2128, 3813]))
else
(if i.val < 3043 then
(if i.val < 3042 then
![1440, 3282]
else
![3210, 3777])
else
(if i.val < 3044 then
![2303, 3814]
else
![3774, 3815])))
else
(if i.val < 3049 then
(if i.val < 3047 then
(if i.val < 3046 then
![3816, 2699]
else
![3817, 2625])
else
(if i.val < 3048 then
![1950, 3818]
else
![193, 3819]))
else
(if i.val < 3051 then
(if i.val < 3050 then
![3820, 3821]
else
![876, 3822])
else
(if i.val < 3052 then
![1098, 3823]
else
(if i.val < 3053 then
![3757, 2783]
else
![2192, 3824])))))
else
(if i.val < 3062 then
(if i.val < 3058 then
(if i.val < 3056 then
(if i.val < 3055 then
![3825, 3826]
else
![3827, 3828])
else
(if i.val < 3057 then
![3829, 3830]
else
![3667, 3831]))
else
(if i.val < 3060 then
(if i.val < 3059 then
![3743, 3832]
else
![787, 3833])
else
(if i.val < 3061 then
![2414, 636]
else
![3834, 3835])))
else
(if i.val < 3066 then
(if i.val < 3064 then
(if i.val < 3063 then
![141, 3270]
else
![3791, 487])
else
(if i.val < 3065 then
![2636, 1726]
else
![3702, 2651]))
else
(if i.val < 3068 then
(if i.val < 3067 then
![2789, 228]
else
![3819, 3836])
else
(if i.val < 3069 then
![3837, 2292]
else
(if i.val < 3070 then
![3725, 3838]
else
![793, 2944]))))))
else
(if i.val < 3088 then
(if i.val < 3079 then
(if i.val < 3075 then
(if i.val < 3073 then
(if i.val < 3072 then
![3758, 3839]
else
![3840, 2686])
else
(if i.val < 3074 then
![1793, 3841]
else
![2428, 1852]))
else
(if i.val < 3077 then
(if i.val < 3076 then
![3842, 3843]
else
![3818, 3376])
else
(if i.val < 3078 then
![271, 2605]
else
![2440, 1409])))
else
(if i.val < 3083 then
(if i.val < 3081 then
(if i.val < 3080 then
![2705, 84]
else
![2588, 459])
else
(if i.val < 3082 then
![3844, 3845]
else
![3846, 2851]))
else
(if i.val < 3085 then
(if i.val < 3084 then
![3847, 617]
else
![3726, 3848])
else
(if i.val < 3086 then
![3849, 3850]
else
(if i.val < 3087 then
![2838, 3530]
else
![3851, 3852])))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
![3249, 3853]
else
![2199, 3854])
else
(if i.val < 3091 then
![399, 1700]
else
![3727, 479]))
else
(if i.val < 3094 then
(if i.val < 3093 then
![3753, 1600]
else
![3855, 3856])
else
(if i.val < 3095 then
![3692, 3857]
else
![2736, 3858])))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
![2336, 2841]
else
![805, 3037])
else
(if i.val < 3099 then
![1011, 2768]
else
![1092, 2772]))
else
(if i.val < 3102 then
(if i.val < 3101 then
![3705, 65]
else
![3859, 660])
else
(if i.val < 3103 then
![3860, 650]
else
(if i.val < 3104 then
![1916, 3861]
else
![2468, 3052]))))))))
else
(if i.val < 3172 then
(if i.val < 3138 then
(if i.val < 3121 then
(if i.val < 3113 then
(if i.val < 3109 then
(if i.val < 3107 then
(if i.val < 3106 then
![3862, 3863]
else
![596, 1868])
else
(if i.val < 3108 then
![1094, 2250]
else
![2887, 1401]))
else
(if i.val < 3111 then
(if i.val < 3110 then
![3864, 1671]
else
![2173, 3865])
else
(if i.val < 3112 then
![3866, 3867]
else
![1585, 2788])))
else
(if i.val < 3117 then
(if i.val < 3115 then
(if i.val < 3114 then
![3865, 3868]
else
![3730, 3869])
else
(if i.val < 3116 then
![391, 3870]
else
![1179, 3871]))
else
(if i.val < 3119 then
(if i.val < 3118 then
![2150, 3872]
else
![3872, 3531])
else
(if i.val < 3120 then
![1064, 3873]
else
![3874, 435]))))
else
(if i.val < 3129 then
(if i.val < 3125 then
(if i.val < 3123 then
(if i.val < 3122 then
![2488, 1470]
else
![3875, 184])
else
(if i.val < 3124 then
![3876, 581]
else
![1670, 3875]))
else
(if i.val < 3127 then
(if i.val < 3126 then
![3369, 2820]
else
![3867, 2958])
else
(if i.val < 3128 then
![2262, 2524]
else
![1155, 2274])))
else
(if i.val < 3133 then
(if i.val < 3131 then
(if i.val < 3130 then
![2338, 3877]
else
![2821, 3878])
else
(if i.val < 3132 then
![2315, 3879]
else
![2322, 3880]))
else
(if i.val < 3135 then
(if i.val < 3134 then
![3881, 3882]
else
![3789, 3883])
else
(if i.val < 3136 then
![3879, 93]
else
(if i.val < 3137 then
![3754, 2564]
else
![3884, 1287]))))))
else
(if i.val < 3155 then
(if i.val < 3146 then
(if i.val < 3142 then
(if i.val < 3140 then
(if i.val < 3139 then
![3885, 656]
else
![3886, 3887])
else
(if i.val < 3141 then
![2425, 3888]
else
![3889, 3057]))
else
(if i.val < 3144 then
(if i.val < 3143 then
![3863, 2013]
else
![3887, 3890])
else
(if i.val < 3145 then
![1036, 3891]
else
![3892, 3893])))
else
(if i.val < 3150 then
(if i.val < 3148 then
(if i.val < 3147 then
![3745, 3894]
else
![3788, 618])
else
(if i.val < 3149 then
![2562, 3895]
else
![3896, 3897]))
else
(if i.val < 3152 then
(if i.val < 3151 then
![522, 3898]
else
![3895, 3090])
else
(if i.val < 3153 then
![1708, 3786]
else
(if i.val < 3154 then
![1674, 2339]
else
![364, 3899])))))
else
(if i.val < 3163 then
(if i.val < 3159 then
(if i.val < 3157 then
(if i.val < 3156 then
![2358, 3816]
else
![2606, 3900])
else
(if i.val < 3158 then
![2270, 2419]
else
![3901, 554]))
else
(if i.val < 3161 then
(if i.val < 3160 then
![3902, 2922]
else
![3900, 3295])
else
(if i.val < 3162 then
![3903, 3904]
else
![3744, 542])))
else
(if i.val < 3167 then
(if i.val < 3165 then
(if i.val < 3164 then
![1176, 3905]
else
![2153, 3906])
else
(if i.val < 3166 then
![3712, 3907]
else
![3762, 3908]))
else
(if i.val < 3169 then
(if i.val < 3168 then
![1218, 2627]
else
![3625, 1238])
else
(if i.val < 3170 then
![949, 91]
else
(if i.val < 3171 then
![3907, 3781]
else
![2570, 2704])))))))
else
(if i.val < 3206 then
(if i.val < 3189 then
(if i.val < 3180 then
(if i.val < 3176 then
(if i.val < 3174 then
(if i.val < 3173 then
![2413, 3068]
else
![2203, 1014])
else
(if i.val < 3175 then
![3909, 1691]
else
![2475, 2764]))
else
(if i.val < 3178 then
(if i.val < 3177 then
![3858, 3910]
else
![2525, 3080])
else
(if i.val < 3179 then
![3911, 501]
else
![3747, 3912])))
else
(if i.val < 3184 then
(if i.val < 3182 then
(if i.val < 3181 then
![2144, 56]
else
![3430, 69])
else
(if i.val < 3183 then
![2264, 1882]
else
![2845, 3721]))
else
(if i.val < 3186 then
(if i.val < 3185 then
![3913, 494]
else
![3914, 3432])
else
(if i.val < 3187 then
![200, 3915]
else
(if i.val < 3188 then
![3719, 1319]
else
![3916, 492])))))
else
(if i.val < 3197 then
(if i.val < 3193 then
(if i.val < 3191 then
(if i.val < 3190 then
![3917, 3918]
else
![145, 3287])
else
(if i.val < 3192 then
![3868, 2027]
else
![3483, 1488]))
else
(if i.val < 3195 then
(if i.val < 3194 then
![2513, 3860]
else
![3919, 3497])
else
(if i.val < 3196 then
![2324, 1446]
else
![2519, 2302])))
else
(if i.val < 3201 then
(if i.val < 3199 then
(if i.val < 3198 then
![3656, 3696]
else
![3241, 3920])
else
(if i.val < 3200 then
![898, 2442]
else
![1057, 2316]))
else
(if i.val < 3203 then
(if i.val < 3202 then
![3406, 2730]
else
![1109, 2163])
else
(if i.val < 3204 then
![1052, 3921]
else
(if i.val < 3205 then
![2508, 3922]
else
![3143, 1500]))))))
else
(if i.val < 3223 then
(if i.val < 3214 then
(if i.val < 3210 then
(if i.val < 3208 then
(if i.val < 3207 then
![2489, 676]
else
![1342, 3923])
else
(if i.val < 3209 then
![2470, 3924]
else
![3871, 3925]))
else
(if i.val < 3212 then
(if i.val < 3211 then
![2298, 3926]
else
![3927, 2533])
else
(if i.val < 3213 then
![2409, 3928]
else
![3929, 3930])))
else
(if i.val < 3218 then
(if i.val < 3216 then
(if i.val < 3215 then
![3196, 452]
else
![2168, 3931])
else
(if i.val < 3217 then
![990, 1334]
else
![3932, 1368]))
else
(if i.val < 3220 then
(if i.val < 3219 then
![3801, 3933]
else
![3934, 1646])
else
(if i.val < 3221 then
![2388, 3935]
else
(if i.val < 3222 then
![3936, 2856]
else
![2403, 2742])))))
else
(if i.val < 3231 then
(if i.val < 3227 then
(if i.val < 3225 then
(if i.val < 3224 then
![2245, 3937]
else
![1684, 695])
else
(if i.val < 3226 then
![1026, 2675]
else
![438, 1498]))
else
(if i.val < 3229 then
(if i.val < 3228 then
![3938, 2911]
else
![3695, 1332])
else
(if i.val < 3230 then
![3678, 3939]
else
![3893, 3203])))
else
(if i.val < 3235 then
(if i.val < 3233 then
(if i.val < 3232 then
![2739, 3940]
else
![553, 3941])
else
(if i.val < 3234 then
![3815, 2706]
else
![3841, 3942]))
else
(if i.val < 3237 then
(if i.val < 3236 then
![1013, 1486]
else
![446, 3943])
else
(if i.val < 3238 then
![3944, 158]
else
(if i.val < 3239 then
![3945, 3946]
else
![3946, 3947])))))))))))
else
(if i.val < 3780 then
(if i.val < 3510 then
(if i.val < 3375 then
(if i.val < 3307 then
(if i.val < 3273 then
(if i.val < 3256 then
(if i.val < 3248 then
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
![465, 3948]
else
![3607, 3552])
else
(if i.val < 3243 then
![3764, 3949]
else
![3906, 3454]))
else
(if i.val < 3246 then
(if i.val < 3245 then
![2443, 1867]
else
![2863, 3950])
else
(if i.val < 3247 then
![3951, 2649]
else
![1087, 2771])))
else
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
![1378, 3205]
else
![546, 3643])
else
(if i.val < 3251 then
![2807, 1274]
else
![2134, 3952]))
else
(if i.val < 3254 then
(if i.val < 3253 then
![3797, 3071]
else
![1194, 3019])
else
(if i.val < 3255 then
![3953, 1632]
else
![3741, 1879]))))
else
(if i.val < 3264 then
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
![3954, 3864]
else
![3955, 3956])
else
(if i.val < 3259 then
![3957, 3301]
else
![1216, 688]))
else
(if i.val < 3262 then
(if i.val < 3261 then
![3161, 3567]
else
![2903, 3389])
else
(if i.val < 3263 then
![3958, 1364]
else
![1035, 2827])))
else
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
![2720, 3959]
else
![3882, 3960])
else
(if i.val < 3267 then
![2776, 3961]
else
![204, 3962]))
else
(if i.val < 3270 then
(if i.val < 3269 then
![3526, 3704]
else
![979, 3963])
else
(if i.val < 3271 then
![1938, 2623]
else
(if i.val < 3272 then
![889, 1158]
else
![2612, 2968]))))))
else
(if i.val < 3290 then
(if i.val < 3281 then
(if i.val < 3277 then
(if i.val < 3275 then
(if i.val < 3274 then
![3832, 3964]
else
![3457, 165])
else
(if i.val < 3276 then
![3964, 3491]
else
![3836, 3800]))
else
(if i.val < 3279 then
(if i.val < 3278 then
![3965, 2799]
else
![3783, 2314])
else
(if i.val < 3280 then
![2581, 3966]
else
![3773, 1441])))
else
(if i.val < 3285 then
(if i.val < 3283 then
(if i.val < 3282 then
![3966, 1425]
else
![3770, 3795])
else
(if i.val < 3284 then
![1131, 3967]
else
![2913, 3968]))
else
(if i.val < 3287 then
(if i.val < 3286 then
![2446, 2826]
else
![2473, 3969])
else
(if i.val < 3288 then
![3970, 3896]
else
(if i.val < 3289 then
![896, 3971]
else
![3972, 3973])))))
else
(if i.val < 3298 then
(if i.val < 3294 then
(if i.val < 3292 then
(if i.val < 3291 then
![2521, 3412]
else
![2630, 2696])
else
(if i.val < 3293 then
![3974, 1306]
else
![2364, 1276]))
else
(if i.val < 3296 then
(if i.val < 3295 then
![3975, 3976]
else
![978, 3955])
else
(if i.val < 3297 then
![2500, 3977]
else
![3978, 2127])))
else
(if i.val < 3302 then
(if i.val < 3300 then
(if i.val < 3299 then
![802, 3979]
else
![909, 2987])
else
(if i.val < 3301 then
![3980, 2666]
else
![2480, 3851]))
else
(if i.val < 3304 then
(if i.val < 3303 then
![3981, 2554]
else
![3814, 2511])
else
(if i.val < 3305 then
![3922, 3116]
else
(if i.val < 3306 then
![2743, 3178]
else
![3962, 3209])))))))
else
(if i.val < 3341 then
(if i.val < 3324 then
(if i.val < 3315 then
(if i.val < 3311 then
(if i.val < 3309 then
(if i.val < 3308 then
![1944, 3982]
else
![1714, 2921])
else
(if i.val < 3310 then
![3983, 2727]
else
![3771, 3984]))
else
(if i.val < 3313 then
(if i.val < 3312 then
![2850, 3755]
else
![3985, 3889])
else
(if i.val < 3314 then
![2729, 727]
else
![3986, 1586])))
else
(if i.val < 3319 then
(if i.val < 3317 then
(if i.val < 3316 then
![2405, 3987]
else
![2227, 595])
else
(if i.val < 3318 then
![3988, 1358]
else
![3828, 17]))
else
(if i.val < 3321 then
(if i.val < 3320 then
![3989, 2781]
else
![2932, 2182])
else
(if i.val < 3322 then
![1163, 3482]
else
(if i.val < 3323 then
![2539, 3990]
else
![3991, 549])))))
else
(if i.val < 3332 then
(if i.val < 3328 then
(if i.val < 3326 then
(if i.val < 3325 then
![3179, 2402]
else
![963, 530])
else
(if i.val < 3327 then
![2435, 468]
else
![3992, 3993]))
else
(if i.val < 3330 then
(if i.val < 3329 then
![1056, 1421]
else
![3931, 1339])
else
(if i.val < 3331 then
![157, 2733]
else
![3993, 1584])))
else
(if i.val < 3336 then
(if i.val < 3334 then
(if i.val < 3333 then
![1089, 2956]
else
![3994, 3500])
else
(if i.val < 3335 then
![3838, 604]
else
![916, 3157]))
else
(if i.val < 3338 then
(if i.val < 3337 then
![1407, 2353]
else
![3995, 3902])
else
(if i.val < 3339 then
![3861, 3996]
else
(if i.val < 3340 then
![3883, 3997]
else
![312, 3917]))))))
else
(if i.val < 3358 then
(if i.val < 3349 then
(if i.val < 3345 then
(if i.val < 3343 then
(if i.val < 3342 then
![3904, 3998]
else
![3835, 3999])
else
(if i.val < 3344 then
![3183, 4000]
else
![4001, 1203]))
else
(if i.val < 3347 then
(if i.val < 3346 then
![3848, 4002]
else
![3464, 194])
else
(if i.val < 3348 then
![2200, 4003]
else
![1659, 1923])))
else
(if i.val < 3353 then
(if i.val < 3351 then
(if i.val < 3350 then
![2259, 2712]
else
![4004, 2819])
else
(if i.val < 3352 then
![3969, 1436]
else
![3830, 1687]))
else
(if i.val < 3355 then
(if i.val < 3354 then
![4005, 4006]
else
![3735, 97])
else
(if i.val < 3356 then
![2664, 250]
else
(if i.val < 3357 then
![659, 4007]
else
![3873, 2755])))))
else
(if i.val < 3366 then
(if i.val < 3362 then
(if i.val < 3360 then
(if i.val < 3359 then
![1847, 722]
else
![4008, 1822])
else
(if i.val < 3361 then
![3792, 4009]
else
![2641, 2979]))
else
(if i.val < 3364 then
(if i.val < 3363 then
![3746, 4010]
else
![2249, 4011])
else
(if i.val < 3365 then
![1113, 1419]
else
![3987, 599])))
else
(if i.val < 3370 then
(if i.val < 3368 then
(if i.val < 3367 then
![168, 1688]
else
![2892, 575])
else
(if i.val < 3369 then
![4012, 2900]
else
![1428, 4013]))
else
(if i.val < 3372 then
(if i.val < 3371 then
![4013, 3261]
else
![3805, 1055])
else
(if i.val < 3373 then
![3677, 4014]
else
(if i.val < 3374 then
![4015, 4016]
else
![4017, 3885]))))))))
else
(if i.val < 3442 then
(if i.val < 3408 then
(if i.val < 3391 then
(if i.val < 3383 then
(if i.val < 3379 then
(if i.val < 3377 then
(if i.val < 3376 then
![3928, 1820]
else
![3557, 2637])
else
(if i.val < 3378 then
![4018, 1437]
else
![2534, 1521]))
else
(if i.val < 3381 then
(if i.val < 3380 then
![4019, 230]
else
![3960, 1824])
else
(if i.val < 3382 then
![2352, 4020]
else
![3785, 3424])))
else
(if i.val < 3387 then
(if i.val < 3385 then
(if i.val < 3384 then
![3888, 3291]
else
![3095, 3229])
else
(if i.val < 3386 then
![3812, 4021]
else
![4022, 4023]))
else
(if i.val < 3389 then
(if i.val < 3388 then
![3689, 4024]
else
![1547, 3218])
else
(if i.val < 3390 then
![901, 2471]
else
![3822, 4025]))))
else
(if i.val < 3399 then
(if i.val < 3395 then
(if i.val < 3393 then
(if i.val < 3392 then
![2689, 4026]
else
![1819, 1895])
else
(if i.val < 3394 then
![3739, 4027]
else
![3808, 80]))
else
(if i.val < 3397 then
(if i.val < 3396 then
![4028, 235]
else
![2765, 3326])
else
(if i.val < 3398 then
![1185, 4029]
else
![4029, 1457])))
else
(if i.val < 3403 then
(if i.val < 3401 then
(if i.val < 3400 then
![4030, 2682]
else
![4031, 2410])
else
(if i.val < 3402 then
![2492, 1800]
else
![3853, 4032]))
else
(if i.val < 3405 then
(if i.val < 3404 then
![4033, 1429]
else
![4034, 3107])
else
(if i.val < 3406 then
![3979, 4035]
else
(if i.val < 3407 then
![1734, 2587]
else
![3324, 2870]))))))
else
(if i.val < 3425 then
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
![1146, 4036]
else
![4037, 2547])
else
(if i.val < 3411 then
![3626, 3225]
else
![4038, 4039]))
else
(if i.val < 3414 then
(if i.val < 3413 then
![3532, 4040]
else
![2191, 67])
else
(if i.val < 3415 then
![4041, 2931]
else
![2265, 4042])))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
![970, 3533]
else
![2515, 1605])
else
(if i.val < 3419 then
![3912, 4043]
else
![3845, 4044]))
else
(if i.val < 3422 then
(if i.val < 3421 then
![4020, 3144]
else
![2286, 724])
else
(if i.val < 3423 then
![3924, 658]
else
(if i.val < 3424 then
![2545, 4045]
else
![4046, 3916])))))
else
(if i.val < 3433 then
(if i.val < 3429 then
(if i.val < 3427 then
(if i.val < 3426 then
![3948, 3488]
else
![708, 4047])
else
(if i.val < 3428 then
![4048, 2989]
else
![2602, 4049]))
else
(if i.val < 3431 then
(if i.val < 3430 then
![4050, 4051]
else
![3571, 3978])
else
(if i.val < 3432 then
![2550, 4028]
else
![895, 4052])))
else
(if i.val < 3437 then
(if i.val < 3435 then
(if i.val < 3434 then
![4025, 4053]
else
![2814, 3644])
else
(if i.val < 3436 then
![1549, 3508]
else
![1017, 4054]))
else
(if i.val < 3439 then
(if i.val < 3438 then
![4055, 3050]
else
![3940, 4056])
else
(if i.val < 3440 then
![4057, 754]
else
(if i.val < 3441 then
![3221, 2589]
else
![4058, 3859])))))))
else
(if i.val < 3476 then
(if i.val < 3459 then
(if i.val < 3450 then
(if i.val < 3446 then
(if i.val < 3444 then
(if i.val < 3443 then
![520, 1663]
else
![2748, 3536])
else
(if i.val < 3445 then
![2871, 4059]
else
![4059, 3319]))
else
(if i.val < 3448 then
(if i.val < 3447 then
![1597, 3171]
else
![1346, 4060])
else
(if i.val < 3449 then
![4061, 704]
else
![1414, 1709])))
else
(if i.val < 3454 then
(if i.val < 3452 then
(if i.val < 3451 then
![668, 1431]
else
![3654, 3686])
else
(if i.val < 3453 then
![4062, 1719]
else
![4063, 2063]))
else
(if i.val < 3456 then
(if i.val < 3455 then
![3449, 3780]
else
![143, 665])
else
(if i.val < 3457 then
![831, 3846]
else
(if i.val < 3458 then
![1567, 4064]
else
![1023, 4065])))))
else
(if i.val < 3467 then
(if i.val < 3463 then
(if i.val < 3461 then
(if i.val < 3460 then
![2890, 4066]
else
![2164, 699])
else
(if i.val < 3462 then
![3935, 1712]
else
![2905, 3119]))
else
(if i.val < 3465 then
(if i.val < 3464 then
![475, 3414]
else
![319, 1945])
else
(if i.val < 3466 then
![2701, 3124]
else
![3930, 683])))
else
(if i.val < 3471 then
(if i.val < 3469 then
(if i.val < 3468 then
![3779, 4067]
else
![2643, 4068])
else
(if i.val < 3470 then
![2530, 3058]
else
![4069, 4070]))
else
(if i.val < 3473 then
(if i.val < 3472 then
![3722, 4071]
else
![3127, 1760])
else
(if i.val < 3474 then
![1435, 1531]
else
(if i.val < 3475 then
![4072, 756]
else
![4060, 4073]))))))
else
(if i.val < 3493 then
(if i.val < 3484 then
(if i.val < 3480 then
(if i.val < 3478 then
(if i.val < 3477 then
![3222, 1756]
else
![2275, 3077])
else
(if i.val < 3479 then
![3569, 4074]
else
![1686, 3577]))
else
(if i.val < 3482 then
(if i.val < 3481 then
![2156, 4075]
else
![4075, 4076])
else
(if i.val < 3483 then
![3347, 4077]
else
![2433, 2491])))
else
(if i.val < 3488 then
(if i.val < 3486 then
(if i.val < 3485 then
![3977, 1735]
else
![4078, 4079])
else
(if i.val < 3487 then
![3793, 4080]
else
![3869, 3980]))
else
(if i.val < 3490 then
(if i.val < 3489 then
![3348, 3862]
else
![1167, 4081])
else
(if i.val < 3491 then
![2840, 4082]
else
(if i.val < 3492 then
![2685, 4083]
else
![4084, 2326])))))
else
(if i.val < 3501 then
(if i.val < 3497 then
(if i.val < 3495 then
(if i.val < 3494 then
![3918, 3676]
else
![2450, 4085])
else
(if i.val < 3496 then
![1887, 4086]
else
![3236, 3711]))
else
(if i.val < 3499 then
(if i.val < 3498 then
![2708, 3892]
else
![4087, 4088])
else
(if i.val < 3500 then
![1183, 224]
else
![2267, 2715])))
else
(if i.val < 3505 then
(if i.val < 3503 then
(if i.val < 3502 then
![4089, 3374]
else
![2881, 63])
else
(if i.val < 3504 then
![4002, 1753]
else
![1990, 1395]))
else
(if i.val < 3507 then
(if i.val < 3506 then
![2113, 3661]
else
![3224, 3975])
else
(if i.val < 3508 then
![4090, 4091]
else
(if i.val < 3509 then
![386, 3199]
else
![2366, 3487])))))))))
else
(if i.val < 3645 then
(if i.val < 3577 then
(if i.val < 3543 then
(if i.val < 3526 then
(if i.val < 3518 then
(if i.val < 3514 then
(if i.val < 3512 then
(if i.val < 3511 then
![2526, 1976]
else
![4092, 622])
else
(if i.val < 3513 then
![4093, 4034]
else
![3905, 3246]))
else
(if i.val < 3516 then
(if i.val < 3515 then
![1038, 21]
else
![4086, 308])
else
(if i.val < 3517 then
![2184, 2552]
else
![3509, 3784])))
else
(if i.val < 3522 then
(if i.val < 3520 then
(if i.val < 3519 then
![1890, 2962]
else
![3891, 3953])
else
(if i.val < 3521 then
![3238, 3927]
else
![2393, 4094]))
else
(if i.val < 3524 then
(if i.val < 3523 then
![2506, 1454]
else
![2206, 3803])
else
(if i.val < 3525 then
![150, 4095]
else
![4096, 3297]))))
else
(if i.val < 3534 then
(if i.val < 3530 then
(if i.val < 3528 then
(if i.val < 3527 then
![2003, 1808]
else
![4066, 644])
else
(if i.val < 3529 then
![4097, 3456]
else
![2329, 991]))
else
(if i.val < 3532 then
(if i.val < 3531 then
![857, 2761]
else
![3472, 4098])
else
(if i.val < 3533 then
![2855, 4099]
else
![2670, 2379])))
else
(if i.val < 3538 then
(if i.val < 3536 then
(if i.val < 3535 then
![3495, 2779]
else
![4100, 4101])
else
(if i.val < 3537 then
![361, 4102]
else
![3823, 4103]))
else
(if i.val < 3540 then
(if i.val < 3539 then
![1516, 3593]
else
![1165, 1617])
else
(if i.val < 3541 then
![2421, 4104]
else
(if i.val < 3542 then
![434, 4105]
else
![3925, 1511]))))))
else
(if i.val < 3560 then
(if i.val < 3551 then
(if i.val < 3547 then
(if i.val < 3545 then
(if i.val < 3544 then
![198, 4106]
else
![2586, 3345])
else
(if i.val < 3546 then
![2847, 3598]
else
![1718, 3377]))
else
(if i.val < 3549 then
(if i.val < 3548 then
![4107, 1957]
else
![2880, 1653])
else
(if i.val < 3550 then
![3996, 734]
else
![4045, 3272])))
else
(if i.val < 3555 then
(if i.val < 3553 then
(if i.val < 3552 then
![3790, 3364]
else
![2787, 4050])
else
(if i.val < 3554 then
![4108, 3351]
else
![2679, 1321]))
else
(if i.val < 3557 then
(if i.val < 3556 then
![3939, 277]
else
![1610, 3078])
else
(if i.val < 3558 then
![4006, 685]
else
(if i.val < 3559 then
![907, 2797]
else
![2661, 3986])))))
else
(if i.val < 3568 then
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
![4109, 4110]
else
![4111, 2304])
else
(if i.val < 3563 then
![2844, 3914]
else
![2639, 4112]))
else
(if i.val < 3566 then
(if i.val < 3565 then
![2697, 1955]
else
![4112, 2096])
else
(if i.val < 3567 then
![3693, 4113]
else
![4065, 4114])))
else
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
![2895, 1848]
else
![3687, 4115])
else
(if i.val < 3571 then
![4116, 521]
else
![2812, 4097]))
else
(if i.val < 3574 then
(if i.val < 3573 then
![3999, 3004]
else
![2741, 2926])
else
(if i.val < 3575 then
![1320, 1540]
else
(if i.val < 3576 then
![4117, 4118]
else
![3480, 3535])))))))
else
(if i.val < 3611 then
(if i.val < 3594 then
(if i.val < 3585 then
(if i.val < 3581 then
(if i.val < 3579 then
(if i.val < 3578 then
![3821, 3278]
else
![4081, 3309])
else
(if i.val < 3580 then
![3961, 3346]
else
![1090, 4119]))
else
(if i.val < 3583 then
(if i.val < 3582 then
![4120, 1353]
else
![4043, 4121])
else
(if i.val < 3584 then
![2854, 4122]
else
![2719, 1773])))
else
(if i.val < 3589 then
(if i.val < 3587 then
(if i.val < 3586 then
![4121, 2355]
else
![4123, 4124])
else
(if i.val < 3588 then
![3973, 4125]
else
![2486, 3759]))
else
(if i.val < 3591 then
(if i.val < 3590 then
![2407, 4126]
else
![3852, 3073])
else
(if i.val < 3592 then
![2806, 3934]
else
(if i.val < 3593 then
![4070, 774]
else
![3982, 4127])))))
else
(if i.val < 3602 then
(if i.val < 3598 then
(if i.val < 3596 then
(if i.val < 3595 then
![4128, 3088]
else
![3523, 4129])
else
(if i.val < 3597 then
![3894, 4130]
else
![2927, 3147]))
else
(if i.val < 3600 then
(if i.val < 3599 then
![3670, 2285]
else
![4079, 4061])
else
(if i.val < 3601 then
![3833, 4131]
else
![4021, 648])))
else
(if i.val < 3606 then
(if i.val < 3604 then
(if i.val < 3603 then
![3372, 4132]
else
![2319, 4133])
else
(if i.val < 3605 then
![4132, 1862]
else
![541, 4108]))
else
(if i.val < 3608 then
(if i.val < 3607 then
![3123, 4134]
else
![965, 2135])
else
(if i.val < 3609 then
![3628, 3989]
else
(if i.val < 3610 then
![3436, 2777]
else
![3720, 4135]))))))
else
(if i.val < 3628 then
(if i.val < 3619 then
(if i.val < 3615 then
(if i.val < 3613 then
(if i.val < 3612 then
![1932, 4136]
else
![4135, 1542])
else
(if i.val < 3614 then
![2796, 4137]
else
![3585, 1870]))
else
(if i.val < 3617 then
(if i.val < 3616 then
![1728, 3434]
else
![3422, 3528])
else
(if i.val < 3618 then
![2657, 4138]
else
![4139, 1758])))
else
(if i.val < 3623 then
(if i.val < 3621 then
(if i.val < 3620 then
![4027, 1722]
else
![4011, 1518])
else
(if i.val < 3622 then
![4124, 3613]
else
![709, 4140]))
else
(if i.val < 3625 then
(if i.val < 3624 then
![3933, 3485]
else
![603, 4141])
else
(if i.val < 3626 then
![4142, 3537]
else
(if i.val < 3627 then
![1666, 4143]
else
![4144, 209])))))
else
(if i.val < 3636 then
(if i.val < 3632 then
(if i.val < 3630 then
(if i.val < 3629 then
![3167, 3419]
else
![1133, 3560])
else
(if i.val < 3631 then
![1767, 3614]
else
![2626, 3120]))
else
(if i.val < 3634 then
(if i.val < 3633 then
![2504, 3512]
else
![3856, 1550])
else
(if i.val < 3635 then
![1323, 4145]
else
![2383, 3056])))
else
(if i.val < 3640 then
(if i.val < 3638 then
(if i.val < 3637 then
![1601, 4146]
else
![1229, 4147])
else
(if i.val < 3639 then
![4148, 3932]
else
![3411, 4093]))
else
(if i.val < 3642 then
(if i.val < 3641 then
![2454, 4033]
else
![4077, 2775])
else
(if i.val < 3643 then
![4009, 3036]
else
(if i.val < 3644 then
![2236, 4089]
else
![4149, 1069]))))))))
else
(if i.val < 3712 then
(if i.val < 3678 then
(if i.val < 3661 then
(if i.val < 3653 then
(if i.val < 3649 then
(if i.val < 3647 then
(if i.val < 3646 then
![2877, 1411]
else
![4094, 3125])
else
(if i.val < 3648 then
![4150, 4063]
else
![1153, 4151]))
else
(if i.val < 3651 then
(if i.val < 3650 then
![484, 4152]
else
![2510, 237])
else
(if i.val < 3652 then
![4153, 1327]
else
![2449, 4154])))
else
(if i.val < 3657 then
(if i.val < 3655 then
(if i.val < 3654 then
![4155, 1377]
else
![1066, 4022])
else
(if i.val < 3656 then
![4156, 3017]
else
![4157, 1528]))
else
(if i.val < 3659 then
(if i.val < 3658 then
![2793, 3991]
else
![1221, 4158])
else
(if i.val < 3660 then
![3337, 3138]
else
![3968, 3395]))))
else
(if i.val < 3669 then
(if i.val < 3665 then
(if i.val < 3663 then
(if i.val < 3662 then
![2342, 3825]
else
![4159, 1356])
else
(if i.val < 3664 then
![3752, 2906]
else
![4160, 75]))
else
(if i.val < 3667 then
(if i.val < 3666 then
![3399, 1744]
else
![3910, 25])
else
(if i.val < 3668 then
![4138, 809]
else
![208, 790])))
else
(if i.val < 3673 then
(if i.val < 3671 then
(if i.val < 3670 then
![4161, 3002]
else
![2759, 4162])
else
(if i.val < 3672 then
![4125, 1039]
else
![1797, 2801]))
else
(if i.val < 3675 then
(if i.val < 3674 then
![843, 3988]
else
![4163, 3992])
else
(if i.val < 3676 then
![3850, 736]
else
(if i.val < 3677 then
![3306, 519]
else
![2690, 3257]))))))
else
(if i.val < 3695 then
(if i.val < 3686 then
(if i.val < 3682 then
(if i.val < 3680 then
(if i.val < 3679 then
![1384, 4164]
else
![2737, 3496])
else
(if i.val < 3681 then
![4165, 489]
else
![3049, 4166]))
else
(if i.val < 3684 then
(if i.val < 3683 then
![4095, 3103]
else
![4167, 340])
else
(if i.val < 3685 then
![4166, 4168]
else
![4114, 254])))
else
(if i.val < 3690 then
(if i.val < 3688 then
(if i.val < 3687 then
![3897, 747]
else
![1438, 4169])
else
(if i.val < 3689 then
![3308, 3352]
else
![1005, 4150]))
else
(if i.val < 3692 then
(if i.val < 3691 then
![2295, 3492]
else
![3990, 1947])
else
(if i.val < 3693 then
![3181, 2466]
else
(if i.val < 3694 then
![3645, 1114]
else
![4049, 1810])))))
else
(if i.val < 3703 then
(if i.val < 3699 then
(if i.val < 3697 then
(if i.val < 3696 then
![1812, 3421]
else
![3202, 4170])
else
(if i.val < 3698 then
![4010, 4019]
else
![4171, 3044]))
else
(if i.val < 3701 then
(if i.val < 3700 then
![3921, 4120]
else
![3798, 3958])
else
(if i.val < 3702 then
![2936, 1888]
else
![3233, 4172])))
else
(if i.val < 3707 then
(if i.val < 3705 then
(if i.val < 3704 then
![4169, 2399]
else
![1499, 1979])
else
(if i.val < 3706 then
![4146, 3543]
else
![4080, 3385]))
else
(if i.val < 3709 then
(if i.val < 3708 then
![4122, 885]
else
![3146, 3620])
else
(if i.val < 3710 then
![3072, 3240]
else
(if i.val < 3711 then
![513, 4173]
else
![3558, 1])))))))
else
(if i.val < 3746 then
(if i.val < 3729 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
![3335, 433]
else
![3515, 4174])
else
(if i.val < 3715 then
![630, 3742]
else
![3518, 4175]))
else
(if i.val < 3718 then
(if i.val < 3717 then
![4176, 1854]
else
![2559, 1840])
else
(if i.val < 3719 then
![3484, 3596]
else
![1388, 1813])))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
![3647, 3787]
else
![3602, 3849])
else
(if i.val < 3723 then
![4052, 4177]
else
![2773, 4117]))
else
(if i.val < 3726 then
(if i.val < 3725 then
![2151, 4038]
else
![1530, 3105])
else
(if i.val < 3727 then
![2683, 95]
else
(if i.val < 3728 then
![1222, 4178]
else
![3802, 4179])))))
else
(if i.val < 3737 then
(if i.val < 3733 then
(if i.val < 3731 then
(if i.val < 3730 then
![2756, 749]
else
![4180, 4181])
else
(if i.val < 3732 then
![4102, 556]
else
![4131, 4182]))
else
(if i.val < 3735 then
(if i.val < 3734 then
![3804, 3316]
else
![4044, 917])
else
(if i.val < 3736 then
![3437, 4155]
else
![2341, 2005])))
else
(if i.val < 3741 then
(if i.val < 3739 then
(if i.val < 3738 then
![3104, 3584]
else
![1325, 4142])
else
(if i.val < 3740 then
![1908, 4183]
else
![4039, 971]))
else
(if i.val < 3743 then
(if i.val < 3742 then
![786, 3929]
else
![2490, 3994])
else
(if i.val < 3744 then
![3898, 4184]
else
(if i.val < 3745 then
![4170, 2139]
else
![1529, 2126]))))))
else
(if i.val < 3763 then
(if i.val < 3754 then
(if i.val < 3750 then
(if i.val < 3748 then
(if i.val < 3747 then
![1954, 3085]
else
![4185, 2140])
else
(if i.val < 3749 then
![4186, 3590]
else
![4187, 285]))
else
(if i.val < 3752 then
(if i.val < 3751 then
![1804, 3731]
else
![4188, 1815])
else
(if i.val < 3753 then
![3397, 1682]
else
![777, 1842])))
else
(if i.val < 3758 then
(if i.val < 3756 then
(if i.val < 3755 then
![3158, 2579]
else
![126, 1122])
else
(if i.val < 3757 then
![3826, 1656]
else
![462, 3561]))
else
(if i.val < 3760 then
(if i.val < 3759 then
![2695, 1372]
else
![4189, 1399])
else
(if i.val < 3761 then
![1958, 4190]
else
(if i.val < 3762 then
![2297, 1768]
else
![4191, 1657])))))
else
(if i.val < 3771 then
(if i.val < 3767 then
(if i.val < 3765 then
(if i.val < 3764 then
![2517, 4192]
else
![4193, 3265])
else
(if i.val < 3766 then
![1743, 4194]
else
![4195, 375]))
else
(if i.val < 3769 then
(if i.val < 3768 then
![4194, 3903]
else
![1807, 2603])
else
(if i.val < 3770 then
![4115, 4196]
else
![3055, 1633])))
else
(if i.val < 3775 then
(if i.val < 3773 then
(if i.val < 3772 then
![3165, 4197]
else
![2763, 4198])
else
(if i.val < 3774 then
![3599, 3617]
else
![3198, 117]))
else
(if i.val < 3777 then
(if i.val < 3776 then
![4182, 775]
else
![4181, 1681])
else
(if i.val < 3778 then
![3340, 4199]
else
(if i.val < 3779 then
![1417, 2084]
else
![2909, 4200]))))))))))
else
(if i.val < 4050 then
(if i.val < 3915 then
(if i.val < 3847 then
(if i.val < 3813 then
(if i.val < 3796 then
(if i.val < 3788 then
(if i.val < 3784 then
(if i.val < 3782 then
(if i.val < 3781 then
![1661, 1762]
else
![173, 4157])
else
(if i.val < 3783 then
![3937, 4201]
else
![4196, 3653]))
else
(if i.val < 3786 then
(if i.val < 3785 then
![1471, 1901]
else
![1851, 2723])
else
(if i.val < 3787 then
![3843, 2933]
else
![4192, 651])))
else
(if i.val < 3792 then
(if i.val < 3790 then
(if i.val < 3789 then
![4134, 3355]
else
![2532, 4202])
else
(if i.val < 3791 then
![292, 4203]
else
![4099, 329]))
else
(if i.val < 3794 then
(if i.val < 3793 then
![4198, 797]
else
![3311, 2363])
else
(if i.val < 3795 then
![4203, 4180]
else
![4204, 3710]))))
else
(if i.val < 3804 then
(if i.val < 3800 then
(if i.val < 3798 then
(if i.val < 3797 then
![4202, 3911]
else
![1790, 4205])
else
(if i.val < 3799 then
![3040, 1076]
else
![4082, 3694]))
else
(if i.val < 3802 then
(if i.val < 3801 then
![3115, 3428]
else
![3608, 121])
else
(if i.val < 3803 then
![4172, 379]
else
![2760, 3583])))
else
(if i.val < 3808 then
(if i.val < 3806 then
(if i.val < 3805 then
![900, 2467]
else
![4067, 4167])
else
(if i.val < 3807 then
![568, 4206]
else
![1631, 4207]))
else
(if i.val < 3810 then
(if i.val < 3809 then
![3669, 3983]
else
![1537, 4208])
else
(if i.val < 3811 then
![2317, 4187]
else
(if i.val < 3812 then
![2915, 327]
else
![4118, 1091]))))))
else
(if i.val < 3830 then
(if i.val < 3821 then
(if i.val < 3817 then
(if i.val < 3815 then
(if i.val < 3814 then
![3418, 4153]
else
![1894, 3555])
else
(if i.val < 3816 then
![4209, 3666]
else
![1755, 4210]))
else
(if i.val < 3819 then
(if i.val < 3818 then
![1510, 4211]
else
![3264, 356])
else
(if i.val < 3820 then
![2347, 2873]
else
![1699, 3168])))
else
(if i.val < 3825 then
(if i.val < 3823 then
(if i.val < 3822 then
![4212, 858]
else
![4213, 1093])
else
(if i.val < 3824 then
![3586, 3874]
else
![4073, 847]))
else
(if i.val < 3827 then
(if i.val < 3826 then
![3559, 1680]
else
![1432, 147])
else
(if i.val < 3828 then
![3271, 3360]
else
(if i.val < 3829 then
![3162, 3594]
else
![3043, 1490])))))
else
(if i.val < 3838 then
(if i.val < 3834 then
(if i.val < 3832 then
(if i.val < 3831 then
![4214, 2335]
else
![2868, 4215])
else
(if i.val < 3833 then
![3640, 803]
else
![3563, 3938]))
else
(if i.val < 3836 then
(if i.val < 3835 then
![2790, 2055]
else
![3652, 801])
else
(if i.val < 3837 then
![4036, 4057]
else
![1385, 3180])))
else
(if i.val < 3842 then
(if i.val < 3840 then
(if i.val < 3839 then
![3923, 3368]
else
![1571, 3018])
else
(if i.val < 3841 then
![1525, 4216]
else
![3213, 973]))
else
(if i.val < 3844 then
(if i.val < 3843 then
![4207, 4217]
else
![332, 4109])
else
(if i.val < 3845 then
![4199, 2611]
else
(if i.val < 3846 then
![1900, 2296]
else
![3145, 4218])))))))
else
(if i.val < 3881 then
(if i.val < 3864 then
(if i.val < 3855 then
(if i.val < 3851 then
(if i.val < 3849 then
(if i.val < 3848 then
![1502, 3338]
else
![4056, 1903])
else
(if i.val < 3850 then
![4047, 4219]
else
![3527, 3840]))
else
(if i.val < 3853 then
(if i.val < 3852 then
![4104, 4220]
else
![1489, 1162])
else
(if i.val < 3854 then
![4221, 259]
else
![4222, 2829])))
else
(if i.val < 3859 then
(if i.val < 3857 then
(if i.val < 3856 then
![4178, 4223]
else
![3685, 3951])
else
(if i.val < 3858 then
![1729, 4224]
else
![3408, 2022]))
else
(if i.val < 3861 then
(if i.val < 3860 then
![1645, 3776]
else
![4225, 2284])
else
(if i.val < 3862 then
![4226, 3649]
else
(if i.val < 3863 then
![4227, 3658]
else
![3633, 3876])))))
else
(if i.val < 3872 then
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
![303, 4228]
else
![1456, 4229])
else
(if i.val < 3867 then
![3296, 3761]
else
![1776, 4230]))
else
(if i.val < 3870 then
(if i.val < 3869 then
![4230, 3965]
else
![4101, 3405])
else
(if i.val < 3871 then
![3279, 4231]
else
![3697, 2143])))
else
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
![4231, 2129]
else
![4232, 4233])
else
(if i.val < 3875 then
![1455, 4227]
else
![1396, 3524]))
else
(if i.val < 3878 then
(if i.val < 3877 then
![3208, 3663]
else
![3572, 3807])
else
(if i.val < 3879 then
![4228, 3842]
else
(if i.val < 3880 then
![4190, 4087]
else
![3433, 176]))))))
else
(if i.val < 3898 then
(if i.val < 3889 then
(if i.val < 3885 then
(if i.val < 3883 then
(if i.val < 3882 then
![3673, 3581]
else
![3367, 1244])
else
(if i.val < 3884 then
![3494, 2247]
else
![3053, 899]))
else
(if i.val < 3887 then
(if i.val < 3886 then
![4162, 33]
else
![4234, 2632])
else
(if i.val < 3888 then
![3478, 2688]
else
![3248, 4235])))
else
(if i.val < 3893 then
(if i.val < 3891 then
(if i.val < 3890 then
![4236, 854]
else
![3831, 1717])
else
(if i.val < 3892 then
![1443, 835]
else
![1703, 780]))
else
(if i.val < 3895 then
(if i.val < 3894 then
![3723, 4237]
else
![3724, 2071])
else
(if i.val < 3896 then
![4237, 2246]
else
(if i.val < 3897 then
![4129, 908]
else
![1403, 3820])))))
else
(if i.val < 3906 then
(if i.val < 3902 then
(if i.val < 3900 then
(if i.val < 3899 then
![2117, 2862]
else
![4238, 4213])
else
(if i.val < 3901 then
![4210, 4239]
else
![3638, 4240]))
else
(if i.val < 3904 then
(if i.val < 3903 then
![1723, 4241]
else
![3069, 712])
else
(if i.val < 3905 then
![4242, 3417]
else
![1861, 3715])))
else
(if i.val < 3910 then
(if i.val < 3908 then
(if i.val < 3907 then
![4071, 153]
else
![956, 4243])
else
(if i.val < 3909 then
![4208, 3386]
else
![1575, 1156]))
else
(if i.val < 3912 then
(if i.val < 3911 then
![3460, 879]
else
![2879, 3312])
else
(if i.val < 3913 then
![3245, 2198]
else
(if i.val < 3914 then
![1849, 3646]
else
![3642, 4244]))))))))
else
(if i.val < 3982 then
(if i.val < 3948 then
(if i.val < 3931 then
(if i.val < 3923 then
(if i.val < 3919 then
(if i.val < 3917 then
(if i.val < 3916 then
![2221, 3844]
else
![1838, 4245])
else
(if i.val < 3918 then
![1759, 4246]
else
![1924, 136]))
else
(if i.val < 3921 then
(if i.val < 3920 then
![3564, 418]
else
![1636, 3603])
else
(if i.val < 3922 then
![2919, 4247]
else
![3568, 2133])))
else
(if i.val < 3927 then
(if i.val < 3925 then
(if i.val < 3924 then
![2371, 201]
else
![3890, 3447])
else
(if i.val < 3926 then
![4024, 3847]
else
![3553, 4248]))
else
(if i.val < 3929 then
(if i.val < 3928 then
![3984, 4249]
else
![3033, 123])
else
(if i.val < 3930 then
![4250, 3477]
else
![3074, 4251]))))
else
(if i.val < 3939 then
(if i.val < 3935 then
(if i.val < 3933 then
(if i.val < 3932 then
![1450, 3659]
else
![3235, 2263])
else
(if i.val < 3934 then
![4215, 4252]
else
![4205, 4253]))
else
(if i.val < 3937 then
(if i.val < 3936 then
![3601, 3817]
else
![3086, 13])
else
(if i.val < 3938 then
![4254, 3671]
else
![1383, 4255])))
else
(if i.val < 3943 then
(if i.val < 3941 then
(if i.val < 3940 then
![4245, 4256]
else
![2222, 3972])
else
(if i.val < 3942 then
![1493, 4257]
else
![4258, 1120]))
else
(if i.val < 3945 then
(if i.val < 3944 then
![3681, 2608]
else
![3534, 3690])
else
(if i.val < 3946 then
![826, 2310]
else
(if i.val < 3947 then
![3380, 3985]
else
![2804, 3886]))))))
else
(if i.val < 3965 then
(if i.val < 3956 then
(if i.val < 3952 then
(if i.val < 3950 then
(if i.val < 3949 then
![2257, 3827]
else
![4259, 2357])
else
(if i.val < 3951 then
![2578, 2970]
else
![2778, 4195]))
else
(if i.val < 3954 then
(if i.val < 3953 then
![4218, 2351]
else
![3468, 3809])
else
(if i.val < 3955 then
![3357, 3810]
else
![4184, 4260])))
else
(if i.val < 3960 then
(if i.val < 3958 then
(if i.val < 3957 then
![3317, 4261]
else
![3243, 1078])
else
(if i.val < 3959 then
![2138, 2207]
else
![2785, 3751]))
else
(if i.val < 3962 then
(if i.val < 3961 then
![3546, 2390]
else
![4000, 4262])
else
(if i.val < 3963 then
![2331, 4004]
else
(if i.val < 3964 then
![3507, 4263]
else
![4183, 4264])))))
else
(if i.val < 3973 then
(if i.val < 3969 then
(if i.val < 3967 then
(if i.val < 3966 then
![3344, 4265]
else
![3650, 4046])
else
(if i.val < 3968 then
![3185, 4266]
else
![2483, 4165]))
else
(if i.val < 3971 then
(if i.val < 3970 then
![1696, 119]
else
![3529, 4232])
else
(if i.val < 3972 then
![3481, 4267]
else
![563, 3837])))
else
(if i.val < 3977 then
(if i.val < 3975 then
(if i.val < 3974 then
![3130, 3683]
else
![4268, 926])
else
(if i.val < 3976 then
![4269, 1173]
else
![1828, 1102]))
else
(if i.val < 3979 then
(if i.val < 3978 then
![4211, 4225]
else
![3854, 3498])
else
(if i.val < 3980 then
![649, 4270]
else
(if i.val < 3981 then
![3226, 2154]
else
![251, 4271])))))))
else
(if i.val < 4016 then
(if i.val < 3999 then
(if i.val < 3990 then
(if i.val < 3986 then
(if i.val < 3984 then
(if i.val < 3983 then
![3110, 1468]
else
![2872, 4272])
else
(if i.val < 3985 then
![3438, 4273]
else
![538, 3542]))
else
(if i.val < 3988 then
(if i.val < 3987 then
![1839, 4274]
else
![2193, 1223])
else
(if i.val < 3989 then
![4217, 2190]
else
![297, 4275])))
else
(if i.val < 3994 then
(if i.val < 3992 then
(if i.val < 3991 then
![3453, 2301]
else
![3513, 1248])
else
(if i.val < 3993 then
![3736, 3866]
else
![4197, 3909]))
else
(if i.val < 3996 then
(if i.val < 3995 then
![4219, 458]
else
![4173, 4276])
else
(if i.val < 3997 then
![3353, 2535]
else
(if i.val < 3998 then
![3565, 2985]
else
![4054, 4277])))))
else
(if i.val < 4007 then
(if i.val < 4003 then
(if i.val < 4001 then
(if i.val < 4000 then
![3461, 2453]
else
![4051, 4278])
else
(if i.val < 4002 then
![4279, 827]
else
![4241, 3738]))
else
(if i.val < 4005 then
(if i.val < 4004 then
![4280, 2767]
else
![3662, 3682])
else
(if i.val < 4006 then
![4281, 2079]
else
![4252, 4282])))
else
(if i.val < 4011 then
(if i.val < 4009 then
(if i.val < 4008 then
![4282, 2864]
else
![4168, 2884])
else
(if i.val < 4010 then
![3160, 4283]
else
![3519, 3634]))
else
(if i.val < 4013 then
(if i.val < 4012 then
![1777, 4284]
else
![3108, 4285])
else
(if i.val < 4014 then
![2575, 2462]
else
(if i.val < 4015 then
![3591, 4234]
else
![3941, 1053]))))))
else
(if i.val < 4033 then
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
![4064, 2738]
else
![2518, 692])
else
(if i.val < 4019 then
![4007, 2469]
else
![3329, 4286]))
else
(if i.val < 4022 then
(if i.val < 4021 then
![3619, 2392]
else
![4246, 2360])
else
(if i.val < 4023 then
![3589, 2195]
else
![3621, 583])))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
![2313, 4287]
else
![1591, 3995])
else
(if i.val < 4027 then
![2400, 4018]
else
![3304, 3729]))
else
(if i.val < 4030 then
(if i.val < 4029 then
![3141, 2635]
else
![1673, 4288])
else
(if i.val < 4031 then
![3926, 4269]
else
(if i.val < 4032 then
![2866, 1928]
else
![3452, 2120])))))
else
(if i.val < 4041 then
(if i.val < 4037 then
(if i.val < 4035 then
(if i.val < 4034 then
![4270, 3811]
else
![794, 4078])
else
(if i.val < 4036 then
![3230, 420]
else
![4289, 2204]))
else
(if i.val < 4039 then
(if i.val < 4038 then
![3402, 4236]
else
![3899, 2694])
else
(if i.val < 4040 then
![4098, 3919]
else
![4290, 324])))
else
(if i.val < 4045 then
(if i.val < 4043 then
(if i.val < 4042 then
![4074, 3469]
else
![4291, 131])
else
(if i.val < 4044 then
![4286, 1314]
else
![307, 1298]))
else
(if i.val < 4047 then
(if i.val < 4046 then
![1697, 1250]
else
![3878, 825])
else
(if i.val < 4048 then
![2101, 4090]
else
(if i.val < 4049 then
![4271, 3632]
else
![1980, 437])))))))))
else
(if i.val < 4185 then
(if i.val < 4117 then
(if i.val < 4083 then
(if i.val < 4066 then
(if i.val < 4058 then
(if i.val < 4054 then
(if i.val < 4052 then
(if i.val < 4051 then
![3505, 1261]
else
![2141, 4292])
else
(if i.val < 4053 then
![1482, 2577]
else
![4235, 2529]))
else
(if i.val < 4056 then
(if i.val < 4055 then
![4032, 1576]
else
![1751, 2424])
else
(if i.val < 4057 then
![2426, 3936]
else
![3839, 4293])))
else
(if i.val < 4062 then
(if i.val < 4060 then
(if i.val < 4059 then
![4216, 4281]
else
![4292, 3154])
else
(if i.val < 4061 then
![4264, 3913]
else
![819, 4294]))
else
(if i.val < 4064 then
(if i.val < 4063 then
![3680, 4295]
else
![3490, 2456])
else
(if i.val < 4065 then
![1690, 2875]
else
![4255, 3728]))))
else
(if i.val < 4074 then
(if i.val < 4070 then
(if i.val < 4068 then
(if i.val < 4067 then
![3394, 4280]
else
![3610, 4084])
else
(if i.val < 4069 then
![4284, 4296]
else
![4200, 3884]))
else
(if i.val < 4072 then
(if i.val < 4071 then
![4253, 1404]
else
![3942, 3641])
else
(if i.val < 4073 then
![4248, 1451]
else
![4293, 3007])))
else
(if i.val < 4078 then
(if i.val < 4076 then
(if i.val < 4075 then
![3920, 2327]
else
![4164, 4297])
else
(if i.val < 4077 then
![4143, 2680]
else
![3155, 4185]))
else
(if i.val < 4080 then
(if i.val < 4079 then
![4003, 4186]
else
![3325, 3462])
else
(if i.val < 4081 then
![2634, 3954]
else
(if i.val < 4082 then
![789, 4017]
else
![384, 4298]))))))
else
(if i.val < 4100 then
(if i.val < 4091 then
(if i.val < 4087 then
(if i.val < 4085 then
(if i.val < 4084 then
![561, 4299]
else
![4201, 1535])
else
(if i.val < 4086 then
![3664, 2808]
else
![4298, 4191]))
else
(if i.val < 4089 then
(if i.val < 4088 then
![3943, 4300]
else
![4301, 811])
else
(if i.val < 4090 then
![2334, 3450]
else
![4229, 4291])))
else
(if i.val < 4095 then
(if i.val < 4093 then
(if i.val < 4092 then
![3732, 4159]
else
![4240, 2377])
else
(if i.val < 4094 then
![3562, 3733]
else
![3503, 2507]))
else
(if i.val < 4097 then
(if i.val < 4096 then
![4302, 2786]
else
![3092, 1074])
else
(if i.val < 4098 then
![3623, 4001]
else
(if i.val < 4099 then
![1935, 3511]
else
![2585, 2325])))))
else
(if i.val < 4108 then
(if i.val < 4104 then
(if i.val < 4102 then
(if i.val < 4101 then
![3333, 4030]
else
![3548, 4303])
else
(if i.val < 4103 then
![3410, 1037]
else
![4285, 3740]))
else
(if i.val < 4106 then
(if i.val < 4105 then
![2782, 1240]
else
![1025, 2671])
else
(if i.val < 4107 then
![1031, 3775]
else
![1042, 3970])))
else
(if i.val < 4112 then
(if i.val < 4110 then
(if i.val < 4109 then
![4304, 2754]
else
![2924, 3657])
else
(if i.val < 4111 then
![1770, 1967]
else
![3915, 3554]))
else
(if i.val < 4114 then
(if i.val < 4113 then
![4244, 1379]
else
![4305, 2093])
else
(if i.val < 4115 then
![4220, 4031]
else
(if i.val < 4116 then
![274, 4289]
else
![4053, 3423])))))))
else
(if i.val < 4151 then
(if i.val < 4134 then
(if i.val < 4125 then
(if i.val < 4121 then
(if i.val < 4119 then
(if i.val < 4118 then
![3701, 4096]
else
![2406, 4100])
else
(if i.val < 4120 then
![4224, 2599]
else
![4233, 48]))
else
(if i.val < 4123 then
(if i.val < 4122 then
![3445, 3517]
else
![3630, 4041])
else
(if i.val < 4124 then
![3600, 1044]
else
![4239, 4189])))
else
(if i.val < 4129 then
(if i.val < 4127 then
(if i.val < 4126 then
![348, 2496]
else
![4288, 3944])
else
(if i.val < 4128 then
![4276, 2002]
else
![2102, 385]))
else
(if i.val < 4131 then
(if i.val < 4130 then
![2770, 2914]
else
![934, 1136])
else
(if i.val < 4132 then
![4251, 2860]
else
(if i.val < 4133 then
![2859, 2897]
else
![4297, 186])))))
else
(if i.val < 4142 then
(if i.val < 4138 then
(if i.val < 4136 then
(if i.val < 4135 then
![2389, 4123]
else
![4275, 2644])
else
(if i.val < 4137 then
![4306, 2030]
else
![3365, 2543]))
else
(if i.val < 4140 then
(if i.val < 4139 then
![1833, 3881]
else
![3631, 3834])
else
(if i.val < 4141 then
![1865, 1660]
else
![2288, 4012])))
else
(if i.val < 4146 then
(if i.val < 4144 then
(if i.val < 4143 then
![4307, 1304]
else
![4103, 1650])
else
(if i.val < 4145 then
![4223, 3772]
else
![3665, 4058]))
else
(if i.val < 4148 then
(if i.val < 4147 then
![2418, 2822]
else
![4263, 415])
else
(if i.val < 4149 then
![4249, 4254]
else
(if i.val < 4150 then
![4106, 4188]
else
![2464, 2307]))))))
else
(if i.val < 4168 then
(if i.val < 4159 then
(if i.val < 4155 then
(if i.val < 4153 then
(if i.val < 4152 then
![4267, 45]
else
![3575, 4148])
else
(if i.val < 4154 then
![4152, 4204]
else
![3064, 4304]))
else
(if i.val < 4157 then
(if i.val < 4156 then
![4026, 4250]
else
![3106, 2642])
else
(if i.val < 4158 then
![4260, 4116]
else
![4283, 1199])))
else
(if i.val < 4163 then
(if i.val < 4161 then
(if i.val < 4160 then
![1741, 3713]
else
![4261, 4308])
else
(if i.val < 4162 then
![3675, 2571]
else
![3824, 1231]))
else
(if i.val < 4165 then
(if i.val < 4164 then
![4206, 3550]
else
![3963, 4160])
else
(if i.val < 4166 then
![4299, 4111]
else
(if i.val < 4167 then
![867, 4128]
else
![3691, 2832])))))
else
(if i.val < 4176 then
(if i.val < 4172 then
(if i.val < 4170 then
(if i.val < 4169 then
![3813, 3570]
else
![3616, 3945])
else
(if i.val < 4171 then
![2340, 220]
else
![4140, 3716]))
else
(if i.val < 4174 then
(if i.val < 4173 then
![2809, 3084]
else
![3475, 4037])
else
(if i.val < 4175 then
![4309, 400]
else
![2830, 4008])))
else
(if i.val < 4180 then
(if i.val < 4178 then
(if i.val < 4177 then
![2573, 3855]
else
![3102, 4310])
else
(if i.val < 4179 then
![4136, 2818]
else
![4266, 3799]))
else
(if i.val < 4182 then
(if i.val < 4181 then
![3698, 4149]
else
![3806, 1062])
else
(if i.val < 4183 then
![4083, 4055]
else
(if i.val < 4184 then
![3880, 3128]
else
![3471, 2893]))))))))
else
(if i.val < 4252 then
(if i.val < 4218 then
(if i.val < 4201 then
(if i.val < 4193 then
(if i.val < 4189 then
(if i.val < 4187 then
(if i.val < 4186 then
![4243, 1766]
else
![4088, 4107])
else
(if i.val < 4188 then
![1085, 3981]
else
![2423, 5]))
else
(if i.val < 4191 then
(if i.val < 4190 then
![4278, 4302]
else
![2842, 4311])
else
(if i.val < 4192 then
![3388, 4307]
else
![3624, 0])))
else
(if i.val < 4197 then
(if i.val < 4195 then
(if i.val < 4194 then
![4296, 1284]
else
![2124, 2975])
else
(if i.val < 4196 then
![2308, 2395]
else
![3547, 2831]))
else
(if i.val < 4199 then
(if i.val < 4198 then
![473, 3609]
else
![4273, 510])
else
(if i.val < 4200 then
![4014, 222]
else
![1387, 3200]))))
else
(if i.val < 4209 then
(if i.val < 4205 then
(if i.val < 4203 then
(if i.val < 4202 then
![872, 4163]
else
![2817, 534])
else
(if i.val < 4204 then
![2853, 3448]
else
![2653, 2898]))
else
(if i.val < 4207 then
(if i.val < 4206 then
![2495, 3091]
else
![3870, 4161])
else
(if i.val < 4208 then
![3718, 3008]
else
![4127, 4312])))
else
(if i.val < 4213 then
(if i.val < 4211 then
(if i.val < 4210 then
![2678, 4005]
else
![3967, 3061])
else
(if i.val < 4212 then
![2145, 663]
else
![3748, 4313]))
else
(if i.val < 4215 then
(if i.val < 4214 then
![2361, 4139]
else
![1061, 1611])
else
(if i.val < 4216 then
![3857, 3039]
else
(if i.val < 4217 then
![3474, 4144]
else
![4177, 1711]))))))
else
(if i.val < 4235 then
(if i.val < 4226 then
(if i.val < 4222 then
(if i.val < 4220 then
(if i.val < 4219 then
![2795, 1693]
else
![4154, 4176])
else
(if i.val < 4221 then
![4314, 1580]
else
![3660, 674]))
else
(if i.val < 4224 then
(if i.val < 4223 then
![1328, 3099]
else
![4315, 3122])
else
(if i.val < 4225 then
![3277, 3522]
else
![3956, 1917])))
else
(if i.val < 4230 then
(if i.val < 4228 then
(if i.val < 4227 then
![3908, 4156]
else
![2681, 4316])
else
(if i.val < 4229 then
![3111, 4242]
else
![3971, 4317]))
else
(if i.val < 4232 then
(if i.val < 4231 then
![2662, 3639]
else
![4035, 3651])
else
(if i.val < 4233 then
![4110, 1626]
else
(if i.val < 4234 then
![2441, 1564]
else
![478, 3611])))))
else
(if i.val < 4243 then
(if i.val < 4239 then
(if i.val < 4237 then
(if i.val < 4236 then
![3950, 3094]
else
![3976, 2004])
else
(if i.val < 4238 then
![4311, 4214]
else
![4294, 2902]))
else
(if i.val < 4241 then
(if i.val < 4240 then
![3997, 3769]
else
![4257, 4318])
else
(if i.val < 4242 then
![3952, 3187]
else
![4040, 4048])))
else
(if i.val < 4247 then
(if i.val < 4245 then
(if i.val < 4244 then
![4175, 3442]
else
![4023, 887])
else
(if i.val < 4246 then
![2251, 4238]
else
![3877, 1919]))
else
(if i.val < 4249 then
(if i.val < 4248 then
![3949, 2997]
else
![4272, 3549])
else
(if i.val < 4250 then
![4308, 505]
else
(if i.val < 4251 then
![4262, 3957]
else
![4076, 232])))))))
else
(if i.val < 4286 then
(if i.val < 4269 then
(if i.val < 4260 then
(if i.val < 4256 then
(if i.val < 4254 then
(if i.val < 4253 then
![4130, 2052]
else
![488, 2038])
else
(if i.val < 4255 then
![4105, 3506]
else
![2174, 3276]))
else
(if i.val < 4258 then
(if i.val < 4257 then
![4119, 3242]
else
![4247, 2240])
else
(if i.val < 4259 then
![2385, 3173]
else
![2604, 4319])))
else
(if i.val < 4264 then
(if i.val < 4262 then
(if i.val < 4261 then
![4016, 1906]
else
![4126, 4306])
else
(if i.val < 4263 then
![4141, 3109]
else
![4287, 3341]))
else
(if i.val < 4266 then
(if i.val < 4265 then
![2810, 4226]
else
![865, 4092])
else
(if i.val < 4267 then
![4042, 3409]
else
(if i.val < 4268 then
![4068, 4290]
else
![4313, 3137])))))
else
(if i.val < 4277 then
(if i.val < 4273 then
(if i.val < 4271 then
(if i.val < 4270 then
![2674, 4069]
else
![2825, 3227])
else
(if i.val < 4272 then
![4137, 3400]
else
![2520, 3974]))
else
(if i.val < 4275 then
(if i.val < 4274 then
![3283, 1897]
else
![4151, 4072])
else
(if i.val < 4276 then
![1506, 4193]
else
![2401, 1721])))
else
(if i.val < 4281 then
(if i.val < 4279 then
(if i.val < 4278 then
![4174, 2982]
else
![456, 4171])
else
(if i.val < 4280 then
![4256, 2910]
else
![2628, 338]))
else
(if i.val < 4283 then
(if i.val < 4282 then
![4312, 78]
else
![3947, 3587])
else
(if i.val < 4284 then
![4133, 4221]
else
(if i.val < 4285 then
![4147, 3441]
else
![4091, 29]))))))
else
(if i.val < 4303 then
(if i.val < 4294 then
(if i.val < 4290 then
(if i.val < 4288 then
(if i.val < 4287 then
![635, 4209]
else
![4274, 2299])
else
(if i.val < 4289 then
![4317, 731]
else
![4316, 4279]))
else
(if i.val < 4292 then
(if i.val < 4291 then
![2376, 4062]
else
![4158, 4301])
else
(if i.val < 4293 then
![1823, 4222]
else
![1809, 403])))
else
(if i.val < 4298 then
(if i.val < 4296 then
(if i.val < 4295 then
![3959, 3699]
else
![4113, 577])
else
(if i.val < 4297 then
![4265, 4258]
else
![4179, 4212]))
else
(if i.val < 4300 then
(if i.val < 4299 then
![3566, 3749]
else
![3998, 1742])
else
(if i.val < 4301 then
![2724, 2493]
else
(if i.val < 4302 then
![2692, 4315]
else
![2726, 1965])))))
else
(if i.val < 4311 then
(if i.val < 4307 then
(if i.val < 4305 then
(if i.val < 4304 then
![1363, 4268]
else
![4145, 3465])
else
(if i.val < 4306 then
![4319, 1802]
else
![4303, 4314]))
else
(if i.val < 4309 then
(if i.val < 4308 then
![4300, 816]
else
![3136, 4259])
else
(if i.val < 4310 then
![4318, 1373]
else
![4085, 3093])))
else
(if i.val < 4315 then
(if i.val < 4313 then
(if i.val < 4312 then
![784, 4015]
else
![1749, 2234])
else
(if i.val < 4314 then
![3627, 4305]
else
![3142, 3829]))
else
(if i.val < 4317 then
(if i.val < 4316 then
![3292, 4309]
else
![3501, 1213])
else
(if i.val < 4318 then
![4310, 3901]
else
(if i.val < 4319 then
![4295, 3766]
else
![4277, 881])))))))))))))


end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

def g32p_row03_Nodes00 : Fin 4320 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 3 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 6 then
(if i.val < 5 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 7 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 11 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 14 then
(if i.val < 13 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 15 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 19 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 22 then
(if i.val < 21 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 23 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 27 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 30 then
(if i.val < 29 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 31 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 35 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 38 then
(if i.val < 37 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 39 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]])))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 43 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 46 then
(if i.val < 45 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 47 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 51 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 54 then
(if i.val < 53 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 55 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 59 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 62 then
(if i.val < 61 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 63 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 67 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 70 then
(if i.val < 69 then
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 71 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 75 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 78 then
(if i.val < 77 then
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 79 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 83 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 86 then
(if i.val < 85 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 87 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 91 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 94 then
(if i.val < 93 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 95 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 99 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 102 then
(if i.val < 101 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 103 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 107 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 110 then
(if i.val < 109 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 111 then
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 115 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 118 then
(if i.val < 117 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 119 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 123 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))
else
(if i.val < 126 then
(if i.val < 125 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 127 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row03_Nodes01 : Fin 4320 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 131 then
![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 134 then
(if i.val < 133 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 135 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 139 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 142 then
(if i.val < 141 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 143 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 147 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 150 then
(if i.val < 149 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 151 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 155 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 158 then
(if i.val < 157 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 159 then
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])
else
(if i.val < 163 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 166 then
(if i.val < 165 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 167 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]])
else
(if i.val < 171 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 174 then
(if i.val < 173 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 175 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 179 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 182 then
(if i.val < 181 then
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 183 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 187 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 190 then
(if i.val < 189 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 191 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 195 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 198 then
(if i.val < 197 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 199 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 203 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 206 then
(if i.val < 205 then
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 207 then
![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 211 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 214 then
(if i.val < 213 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 215 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 219 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 222 then
(if i.val < 221 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 223 then
![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 227 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 230 then
(if i.val < 229 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 231 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 235 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 238 then
(if i.val < 237 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 239 then
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 243 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 246 then
(if i.val < 245 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 247 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 251 then
![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 254 then
(if i.val < 253 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 255 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row03_Nodes02 : Fin 4320 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 259 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 262 then
(if i.val < 261 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]])
else
(if i.val < 263 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 267 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]))
else
(if i.val < 270 then
(if i.val < 269 then
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 271 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 275 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 278 then
(if i.val < 277 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 279 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 283 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]))
else
(if i.val < 286 then
(if i.val < 285 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 287 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 291 then
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 294 then
(if i.val < 293 then
![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 295 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 299 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 302 then
(if i.val < 301 then
![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 303 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 307 then
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 310 then
(if i.val < 309 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 311 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 315 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 318 then
(if i.val < 317 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 319 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 323 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 326 then
(if i.val < 325 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 327 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 331 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]))
else
(if i.val < 334 then
(if i.val < 333 then
![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 335 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 339 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 342 then
(if i.val < 341 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 343 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 347 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 350 then
(if i.val < 349 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 351 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]])
else
(if i.val < 355 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 358 then
(if i.val < 357 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 359 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 363 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 366 then
(if i.val < 365 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 367 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 371 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]))
else
(if i.val < 374 then
(if i.val < 373 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 375 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 379 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 382 then
(if i.val < 381 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 383 then
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row03_Nodes03 : Fin 4320 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 387 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 390 then
(if i.val < 389 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 391 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 395 then
![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 398 then
(if i.val < 397 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 399 then
![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 403 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 406 then
(if i.val < 405 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 407 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 411 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 414 then
(if i.val < 413 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 415 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 419 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 422 then
(if i.val < 421 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 423 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 427 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 430 then
(if i.val < 429 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 431 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 435 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 438 then
(if i.val < 437 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 439 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 443 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 446 then
(if i.val < 445 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 447 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 451 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 454 then
(if i.val < 453 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 455 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])
else
(if i.val < 459 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 462 then
(if i.val < 461 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 463 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])
else
(if i.val < 467 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]))
else
(if i.val < 470 then
(if i.val < 469 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 471 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 475 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 478 then
(if i.val < 477 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 479 then
![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 483 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 486 then
(if i.val < 485 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 487 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 491 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]))
else
(if i.val < 494 then
(if i.val < 493 then
![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 495 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 499 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]))
else
(if i.val < 502 then
(if i.val < 501 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 503 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]])))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 507 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 510 then
(if i.val < 509 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 511 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row03_Nodes04 : Fin 4320 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 515 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))
else
(if i.val < 518 then
(if i.val < 517 then
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 519 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 523 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 526 then
(if i.val < 525 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 527 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 531 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 534 then
(if i.val < 533 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 535 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 539 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 542 then
(if i.val < 541 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 543 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 547 then
![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 550 then
(if i.val < 549 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 551 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 555 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]))
else
(if i.val < 558 then
(if i.val < 557 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 559 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 563 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 566 then
(if i.val < 565 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 567 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 571 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 574 then
(if i.val < 573 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 575 then
![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 579 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 582 then
(if i.val < 581 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]])
else
(if i.val < 583 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]])
else
(if i.val < 587 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]))
else
(if i.val < 590 then
(if i.val < 589 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]
else
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 591 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 595 then
![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 598 then
(if i.val < 597 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 599 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 603 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 606 then
(if i.val < 605 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 607 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 611 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 614 then
(if i.val < 613 then
![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 615 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 619 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 622 then
(if i.val < 621 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 623 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]])
else
(if i.val < 627 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 630 then
(if i.val < 629 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 631 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 635 then
![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 638 then
(if i.val < 637 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]])
else
(if i.val < 639 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])))))))


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

def g32p_row03_Nodes05 : Fin 4320 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 643 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 646 then
(if i.val < 645 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 647 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 651 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 654 then
(if i.val < 653 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 655 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]
else
![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 659 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 662 then
(if i.val < 661 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]])
else
(if i.val < 663 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 667 then
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))
else
(if i.val < 670 then
(if i.val < 669 then
![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]])
else
(if i.val < 671 then
![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]])))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]])
else
(if i.val < 675 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]))
else
(if i.val < 678 then
(if i.val < 677 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 679 then
![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 683 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]))
else
(if i.val < 686 then
(if i.val < 685 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]])
else
(if i.val < 687 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]
else
![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 691 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]))
else
(if i.val < 694 then
(if i.val < 693 then
![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])
else
(if i.val < 695 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 699 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]))
else
(if i.val < 702 then
(if i.val < 701 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 703 then
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 707 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]))
else
(if i.val < 710 then
(if i.val < 709 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]])
else
(if i.val < 711 then
![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]])
else
(if i.val < 715 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]))
else
(if i.val < 718 then
(if i.val < 717 then
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]])
else
(if i.val < 719 then
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 723 then
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]))
else
(if i.val < 726 then
(if i.val < 725 then
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]
else
![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])
else
(if i.val < 727 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])
else
(if i.val < 731 then
![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))
else
(if i.val < 734 then
(if i.val < 733 then
![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])
else
(if i.val < 735 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]])))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]
else
![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])
else
(if i.val < 739 then
![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 742 then
(if i.val < 741 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])
else
(if i.val < 743 then
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]
else
![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])
else
(if i.val < 747 then
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]
else
![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))
else
(if i.val < 750 then
(if i.val < 749 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 751 then
![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]])
else
(if i.val < 755 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 758 then
(if i.val < 757 then
![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]])
else
(if i.val < 759 then
![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]])))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]
else
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]])
else
(if i.val < 763 then
![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]
else
![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]))
else
(if i.val < 766 then
(if i.val < 765 then
![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]
else
![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]])
else
(if i.val < 767 then
![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]
else
![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))))))


end HodgeLean.Foundations.Program

end
