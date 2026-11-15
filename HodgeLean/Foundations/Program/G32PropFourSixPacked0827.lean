import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths1Part0000 : Fin 2880 → ℕ :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
3
else
3)
else
(if i.val < 3 then
3
else
3))
else
(if i.val < 6 then
(if i.val < 5 then
3
else
3)
else
(if i.val < 7 then
3
else
3)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
3
else
3)
else
(if i.val < 11 then
3
else
3))
else
(if i.val < 14 then
(if i.val < 13 then
3
else
3)
else
(if i.val < 15 then
3
else
3))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
3
else
3)
else
(if i.val < 19 then
3
else
3))
else
(if i.val < 22 then
(if i.val < 21 then
3
else
3)
else
(if i.val < 23 then
3
else
3)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
3
else
3)
else
(if i.val < 27 then
3
else
3))
else
(if i.val < 30 then
(if i.val < 29 then
3
else
3)
else
(if i.val < 31 then
3
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
3)
else
(if i.val < 35 then
3
else
3))
else
(if i.val < 38 then
(if i.val < 37 then
3
else
3)
else
(if i.val < 39 then
3
else
3)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
3
else
3)
else
(if i.val < 43 then
3
else
3))
else
(if i.val < 46 then
(if i.val < 45 then
3
else
3)
else
(if i.val < 47 then
3
else
3))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
3
else
3)
else
(if i.val < 51 then
3
else
3))
else
(if i.val < 54 then
(if i.val < 53 then
3
else
3)
else
(if i.val < 55 then
3
else
3)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
3
else
3)
else
(if i.val < 59 then
3
else
3))
else
(if i.val < 62 then
(if i.val < 61 then
3
else
3)
else
(if i.val < 63 then
3
else
3))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
3
else
3)
else
(if i.val < 67 then
3
else
3))
else
(if i.val < 70 then
(if i.val < 69 then
3
else
3)
else
(if i.val < 71 then
3
else
3)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
3
else
3)
else
(if i.val < 75 then
3
else
3))
else
(if i.val < 78 then
(if i.val < 77 then
3
else
3)
else
(if i.val < 79 then
3
else
3))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
3
else
3)
else
(if i.val < 83 then
3
else
3))
else
(if i.val < 86 then
(if i.val < 85 then
3
else
3)
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
3)
else
(if i.val < 91 then
3
else
3))
else
(if i.val < 94 then
(if i.val < 93 then
3
else
3)
else
(if i.val < 95 then
3
else
3)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
3
else
3)
else
(if i.val < 99 then
3
else
3))
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
3
else
3)
else
(if i.val < 107 then
3
else
3))
else
(if i.val < 110 then
(if i.val < 109 then
3
else
3)
else
(if i.val < 111 then
3
else
3))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
3
else
3)
else
(if i.val < 115 then
3
else
3))
else
(if i.val < 118 then
(if i.val < 117 then
3
else
3)
else
(if i.val < 119 then
3
else
3)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
3
else
3)
else
(if i.val < 123 then
3
else
3))
else
(if i.val < 126 then
(if i.val < 125 then
3
else
3)
else
(if i.val < 127 then
3
else
3)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
3
else
3)
else
(if i.val < 131 then
3
else
3))
else
(if i.val < 134 then
(if i.val < 133 then
3
else
3)
else
(if i.val < 135 then
3
else
3)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
3
else
3)
else
(if i.val < 139 then
3
else
3))
else
(if i.val < 142 then
(if i.val < 141 then
3
else
3)
else
(if i.val < 143 then
3
else
3))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
3
else
3)
else
(if i.val < 147 then
3
else
3))
else
(if i.val < 150 then
(if i.val < 149 then
3
else
3)
else
(if i.val < 151 then
3
else
3)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
3
else
3)
else
(if i.val < 155 then
3
else
3))
else
(if i.val < 158 then
(if i.val < 157 then
3
else
3)
else
(if i.val < 159 then
3
else
3)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
3
else
3)
else
(if i.val < 163 then
3
else
3))
else
(if i.val < 166 then
(if i.val < 165 then
3
else
3)
else
(if i.val < 167 then
3
else
3)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
3
else
3)
else
(if i.val < 171 then
3
else
3))
else
(if i.val < 174 then
(if i.val < 173 then
3
else
3)
else
(if i.val < 175 then
3
else
3))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
3
else
3)
else
(if i.val < 179 then
3
else
3))
else
(if i.val < 182 then
(if i.val < 181 then
3
else
3)
else
(if i.val < 183 then
3
else
3)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
3
else
3)
else
(if i.val < 187 then
3
else
3))
else
(if i.val < 190 then
(if i.val < 189 then
3
else
3)
else
(if i.val < 191 then
3
else
3))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
3
else
3)
else
(if i.val < 195 then
3
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
3
else
3)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
3
else
3)
else
(if i.val < 203 then
3
else
3))
else
(if i.val < 206 then
(if i.val < 205 then
3
else
3)
else
(if i.val < 207 then
3
else
3))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
3
else
3)
else
(if i.val < 211 then
3
else
3))
else
(if i.val < 214 then
(if i.val < 213 then
3
else
3)
else
(if i.val < 215 then
3
else
3)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
3
else
3)
else
(if i.val < 219 then
3
else
3))
else
(if i.val < 222 then
(if i.val < 221 then
3
else
3)
else
(if i.val < 223 then
3
else
3)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
3
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
3
else
3)
else
(if i.val < 231 then
3
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
3))
else
(if i.val < 238 then
(if i.val < 237 then
3
else
3)
else
(if i.val < 239 then
3
else
3))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
3
else
3)
else
(if i.val < 243 then
3
else
3))
else
(if i.val < 246 then
(if i.val < 245 then
3
else
3)
else
(if i.val < 247 then
3
else
3)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
3
else
3)
else
(if i.val < 251 then
3
else
3))
else
(if i.val < 254 then
(if i.val < 253 then
3
else
3)
else
(if i.val < 255 then
3
else
3))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
3
else
3)
else
(if i.val < 259 then
3
else
3))
else
(if i.val < 262 then
(if i.val < 261 then
3
else
3)
else
(if i.val < 263 then
3
else
3)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
3
else
3)
else
(if i.val < 267 then
3
else
3))
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
3
else
3)
else
(if i.val < 275 then
3
else
3))
else
(if i.val < 278 then
(if i.val < 277 then
3
else
3)
else
(if i.val < 279 then
3
else
3)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
3
else
3)
else
(if i.val < 283 then
3
else
3))
else
(if i.val < 286 then
(if i.val < 285 then
3
else
3)
else
(if i.val < 287 then
3
else
3)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
3
else
3)
else
(if i.val < 291 then
3
else
3))
else
(if i.val < 294 then
(if i.val < 293 then
3
else
3)
else
(if i.val < 295 then
3
else
3)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
3
else
3)
else
(if i.val < 299 then
3
else
3))
else
(if i.val < 302 then
(if i.val < 301 then
3
else
3)
else
(if i.val < 303 then
3
else
3))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
3
else
3)
else
(if i.val < 307 then
3
else
3))
else
(if i.val < 310 then
(if i.val < 309 then
3
else
3)
else
(if i.val < 311 then
3
else
3)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
3
else
3)
else
(if i.val < 315 then
3
else
3))
else
(if i.val < 318 then
(if i.val < 317 then
3
else
3)
else
(if i.val < 319 then
3
else
3))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
3
else
3)
else
(if i.val < 323 then
3
else
3))
else
(if i.val < 326 then
(if i.val < 325 then
3
else
3)
else
(if i.val < 327 then
3
else
3)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
3
else
3)
else
(if i.val < 331 then
3
else
3))
else
(if i.val < 334 then
(if i.val < 333 then
3
else
3)
else
(if i.val < 335 then
3
else
3))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
3
else
3)
else
(if i.val < 339 then
3
else
3))
else
(if i.val < 342 then
(if i.val < 341 then
3
else
3)
else
(if i.val < 343 then
3
else
3)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
3
else
3)
else
(if i.val < 347 then
3
else
3))
else
(if i.val < 350 then
(if i.val < 349 then
3
else
3)
else
(if i.val < 351 then
3
else
3)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
3
else
3)
else
(if i.val < 355 then
3
else
3))
else
(if i.val < 358 then
(if i.val < 357 then
3
else
3)
else
(if i.val < 359 then
3
else
3)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
3
else
3)
else
(if i.val < 363 then
3
else
3))
else
(if i.val < 366 then
(if i.val < 365 then
3
else
3)
else
(if i.val < 367 then
3
else
3))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
3
else
3)
else
(if i.val < 371 then
3
else
3))
else
(if i.val < 374 then
(if i.val < 373 then
3
else
3)
else
(if i.val < 375 then
3
else
3)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
3
else
3)
else
(if i.val < 379 then
3
else
3))
else
(if i.val < 382 then
(if i.val < 381 then
3
else
3)
else
(if i.val < 383 then
3
else
3)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
3
else
3)
else
(if i.val < 387 then
3
else
3))
else
(if i.val < 390 then
(if i.val < 389 then
3
else
3)
else
(if i.val < 391 then
3
else
3)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
3
else
3)
else
(if i.val < 395 then
3
else
3))
else
(if i.val < 398 then
(if i.val < 397 then
3
else
3)
else
(if i.val < 399 then
3
else
3))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
3
else
3)
else
(if i.val < 403 then
3
else
3))
else
(if i.val < 406 then
(if i.val < 405 then
3
else
3)
else
(if i.val < 407 then
3
else
3)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
3
else
3)
else
(if i.val < 411 then
3
else
3))
else
(if i.val < 414 then
(if i.val < 413 then
3
else
3)
else
(if i.val < 415 then
3
else
3)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
3
else
3)
else
(if i.val < 419 then
3
else
3))
else
(if i.val < 422 then
(if i.val < 421 then
3
else
3)
else
(if i.val < 423 then
3
else
3)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
3
else
3)
else
(if i.val < 427 then
3
else
3))
else
(if i.val < 430 then
(if i.val < 429 then
3
else
3)
else
(if i.val < 431 then
3
else
3))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
3
else
3)
else
(if i.val < 435 then
3
else
3))
else
(if i.val < 438 then
(if i.val < 437 then
3
else
3)
else
(if i.val < 439 then
3
else
3)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
3
else
3)
else
(if i.val < 443 then
3
else
3))
else
(if i.val < 446 then
(if i.val < 445 then
3
else
3)
else
(if i.val < 447 then
3
else
3))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
3
else
3)
else
(if i.val < 451 then
3
else
3))
else
(if i.val < 454 then
(if i.val < 453 then
3
else
3)
else
(if i.val < 455 then
3
else
3)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
3
else
3)
else
(if i.val < 459 then
3
else
3))
else
(if i.val < 462 then
(if i.val < 461 then
3
else
3)
else
(if i.val < 463 then
3
else
3))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
3
else
3)
else
(if i.val < 467 then
3
else
3))
else
(if i.val < 470 then
(if i.val < 469 then
3
else
3)
else
(if i.val < 471 then
3
else
3)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
3
else
3)
else
(if i.val < 475 then
3
else
3))
else
(if i.val < 478 then
(if i.val < 477 then
3
else
3)
else
(if i.val < 479 then
3
else
3)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
3
else
3)
else
(if i.val < 483 then
3
else
3))
else
(if i.val < 486 then
(if i.val < 485 then
3
else
3)
else
(if i.val < 487 then
3
else
3)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
3
else
3)
else
(if i.val < 491 then
3
else
3))
else
(if i.val < 494 then
(if i.val < 493 then
3
else
3)
else
(if i.val < 495 then
3
else
3))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
3
else
3)
else
(if i.val < 499 then
3
else
3))
else
(if i.val < 502 then
(if i.val < 501 then
3
else
3)
else
(if i.val < 503 then
3
else
3)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
3
else
3)
else
(if i.val < 507 then
3
else
3))
else
(if i.val < 510 then
(if i.val < 509 then
3
else
3)
else
(if i.val < 511 then
3
else
3)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths1Part0001 : Fin 2880 → ℕ :=
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
3)
else
(if i.val < 515 then
3
else
3))
else
(if i.val < 518 then
(if i.val < 517 then
3
else
3)
else
(if i.val < 519 then
3
else
3)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
3
else
3)
else
(if i.val < 523 then
3
else
3))
else
(if i.val < 526 then
(if i.val < 525 then
3
else
3)
else
(if i.val < 527 then
3
else
3))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
3
else
3)
else
(if i.val < 531 then
3
else
3))
else
(if i.val < 534 then
(if i.val < 533 then
3
else
3)
else
(if i.val < 535 then
3
else
3)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
3
else
3)
else
(if i.val < 539 then
3
else
3))
else
(if i.val < 542 then
(if i.val < 541 then
3
else
3)
else
(if i.val < 543 then
3
else
3)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
3
else
3)
else
(if i.val < 547 then
3
else
3))
else
(if i.val < 550 then
(if i.val < 549 then
3
else
3)
else
(if i.val < 551 then
3
else
3)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
3
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
3)
else
(if i.val < 559 then
3
else
3))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
3
else
3)
else
(if i.val < 563 then
3
else
3))
else
(if i.val < 566 then
(if i.val < 565 then
3
else
3)
else
(if i.val < 567 then
3
else
3)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
3
else
3)
else
(if i.val < 571 then
3
else
3))
else
(if i.val < 574 then
(if i.val < 573 then
3
else
3)
else
(if i.val < 575 then
3
else
3))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
3
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
3
else
3)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
3
else
3)
else
(if i.val < 587 then
3
else
3))
else
(if i.val < 590 then
(if i.val < 589 then
3
else
3)
else
(if i.val < 591 then
3
else
3))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
3
else
3)
else
(if i.val < 595 then
3
else
3))
else
(if i.val < 598 then
(if i.val < 597 then
3
else
3)
else
(if i.val < 599 then
3
else
3)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
3
else
3)
else
(if i.val < 603 then
3
else
3))
else
(if i.val < 606 then
(if i.val < 605 then
3
else
3)
else
(if i.val < 607 then
3
else
3)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
3
else
3)
else
(if i.val < 611 then
3
else
3))
else
(if i.val < 614 then
(if i.val < 613 then
3
else
3)
else
(if i.val < 615 then
3
else
3)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
3
else
3)
else
(if i.val < 619 then
3
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
3
else
3)
else
(if i.val < 627 then
3
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
3
else
3)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
3
else
3)
else
(if i.val < 635 then
3
else
3))
else
(if i.val < 638 then
(if i.val < 637 then
3
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
3))
else
(if i.val < 646 then
(if i.val < 645 then
3
else
3)
else
(if i.val < 647 then
3
else
3)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
3
else
3)
else
(if i.val < 651 then
3
else
3))
else
(if i.val < 654 then
(if i.val < 653 then
3
else
3)
else
(if i.val < 655 then
3
else
3))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
3
else
3)
else
(if i.val < 659 then
3
else
3))
else
(if i.val < 662 then
(if i.val < 661 then
3
else
3)
else
(if i.val < 663 then
3
else
3)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
3
else
3)
else
(if i.val < 667 then
3
else
3))
else
(if i.val < 670 then
(if i.val < 669 then
3
else
3)
else
(if i.val < 671 then
3
else
3)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
3
else
3)
else
(if i.val < 675 then
3
else
3))
else
(if i.val < 678 then
(if i.val < 677 then
3
else
3)
else
(if i.val < 679 then
3
else
3)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
3
else
3)
else
(if i.val < 683 then
3
else
3))
else
(if i.val < 686 then
(if i.val < 685 then
3
else
3)
else
(if i.val < 687 then
3
else
3))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
3
else
3)
else
(if i.val < 691 then
3
else
3))
else
(if i.val < 694 then
(if i.val < 693 then
3
else
3)
else
(if i.val < 695 then
3
else
3)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
3
else
3)
else
(if i.val < 699 then
3
else
3))
else
(if i.val < 702 then
(if i.val < 701 then
3
else
3)
else
(if i.val < 703 then
3
else
3))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
3
else
3)
else
(if i.val < 707 then
3
else
3))
else
(if i.val < 710 then
(if i.val < 709 then
3
else
3)
else
(if i.val < 711 then
3
else
3)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
3
else
3)
else
(if i.val < 715 then
3
else
3))
else
(if i.val < 718 then
(if i.val < 717 then
3
else
3)
else
(if i.val < 719 then
3
else
3))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
3
else
3)
else
(if i.val < 723 then
3
else
3))
else
(if i.val < 726 then
(if i.val < 725 then
3
else
3)
else
(if i.val < 727 then
3
else
3)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
3
else
3)
else
(if i.val < 731 then
3
else
3))
else
(if i.val < 734 then
(if i.val < 733 then
3
else
3)
else
(if i.val < 735 then
3
else
3)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
3
else
3)
else
(if i.val < 739 then
3
else
3))
else
(if i.val < 742 then
(if i.val < 741 then
3
else
3)
else
(if i.val < 743 then
3
else
3)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
3
else
3)
else
(if i.val < 747 then
3
else
3))
else
(if i.val < 750 then
(if i.val < 749 then
3
else
3)
else
(if i.val < 751 then
3
else
3))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
3
else
3)
else
(if i.val < 755 then
3
else
3))
else
(if i.val < 758 then
(if i.val < 757 then
3
else
3)
else
(if i.val < 759 then
3
else
3)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
3
else
3)
else
(if i.val < 763 then
3
else
3))
else
(if i.val < 766 then
(if i.val < 765 then
3
else
3)
else
(if i.val < 767 then
3
else
3))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
3
else
3)
else
(if i.val < 771 then
3
else
3))
else
(if i.val < 774 then
(if i.val < 773 then
3
else
3)
else
(if i.val < 775 then
3
else
3)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
3
else
3)
else
(if i.val < 779 then
3
else
3))
else
(if i.val < 782 then
(if i.val < 781 then
3
else
3)
else
(if i.val < 783 then
3
else
3))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
3
else
3)
else
(if i.val < 787 then
3
else
3))
else
(if i.val < 790 then
(if i.val < 789 then
3
else
3)
else
(if i.val < 791 then
3
else
3)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
3
else
3)
else
(if i.val < 795 then
3
else
3))
else
(if i.val < 798 then
(if i.val < 797 then
3
else
3)
else
(if i.val < 799 then
3
else
3)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
3
else
3)
else
(if i.val < 803 then
3
else
3))
else
(if i.val < 806 then
(if i.val < 805 then
3
else
3)
else
(if i.val < 807 then
3
else
3)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
3
else
3)
else
(if i.val < 811 then
3
else
3))
else
(if i.val < 814 then
(if i.val < 813 then
3
else
3)
else
(if i.val < 815 then
3
else
3))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
3
else
3)
else
(if i.val < 819 then
3
else
3))
else
(if i.val < 822 then
(if i.val < 821 then
3
else
3)
else
(if i.val < 823 then
3
else
3)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
3
else
3)
else
(if i.val < 827 then
3
else
3))
else
(if i.val < 830 then
(if i.val < 829 then
3
else
3)
else
(if i.val < 831 then
3
else
3))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
3
else
3)
else
(if i.val < 835 then
3
else
3))
else
(if i.val < 838 then
(if i.val < 837 then
3
else
3)
else
(if i.val < 839 then
3
else
3)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
3
else
3)
else
(if i.val < 843 then
3
else
3))
else
(if i.val < 846 then
(if i.val < 845 then
3
else
3)
else
(if i.val < 847 then
3
else
3))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
3
else
3)
else
(if i.val < 851 then
3
else
3))
else
(if i.val < 854 then
(if i.val < 853 then
3
else
3)
else
(if i.val < 855 then
3
else
3)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
3
else
3)
else
(if i.val < 859 then
3
else
3))
else
(if i.val < 862 then
(if i.val < 861 then
3
else
3)
else
(if i.val < 863 then
3
else
3)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
3
else
3)
else
(if i.val < 867 then
3
else
3))
else
(if i.val < 870 then
(if i.val < 869 then
3
else
3)
else
(if i.val < 871 then
3
else
3)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
3
else
3)
else
(if i.val < 875 then
3
else
3))
else
(if i.val < 878 then
(if i.val < 877 then
3
else
3)
else
(if i.val < 879 then
3
else
3))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
3
else
3)
else
(if i.val < 883 then
3
else
3))
else
(if i.val < 886 then
(if i.val < 885 then
3
else
3)
else
(if i.val < 887 then
3
else
3)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
3
else
3)
else
(if i.val < 891 then
3
else
3))
else
(if i.val < 894 then
(if i.val < 893 then
3
else
3)
else
(if i.val < 895 then
3
else
3)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
3
else
3)
else
(if i.val < 899 then
3
else
3))
else
(if i.val < 902 then
(if i.val < 901 then
3
else
3)
else
(if i.val < 903 then
3
else
3)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
3
else
3)
else
(if i.val < 907 then
3
else
3))
else
(if i.val < 910 then
(if i.val < 909 then
3
else
3)
else
(if i.val < 911 then
3
else
3))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
3
else
3)
else
(if i.val < 915 then
3
else
3))
else
(if i.val < 918 then
(if i.val < 917 then
3
else
3)
else
(if i.val < 919 then
3
else
3)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
3
else
3)
else
(if i.val < 923 then
3
else
3))
else
(if i.val < 926 then
(if i.val < 925 then
3
else
3)
else
(if i.val < 927 then
3
else
3)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
3
else
3)
else
(if i.val < 931 then
3
else
3))
else
(if i.val < 934 then
(if i.val < 933 then
3
else
3)
else
(if i.val < 935 then
3
else
3)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
3
else
3)
else
(if i.val < 939 then
3
else
3))
else
(if i.val < 942 then
(if i.val < 941 then
3
else
3)
else
(if i.val < 943 then
3
else
3))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
3
else
3)
else
(if i.val < 947 then
3
else
3))
else
(if i.val < 950 then
(if i.val < 949 then
3
else
3)
else
(if i.val < 951 then
3
else
3)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
3
else
3)
else
(if i.val < 955 then
3
else
3))
else
(if i.val < 958 then
(if i.val < 957 then
3
else
3)
else
(if i.val < 959 then
3
else
3))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
3
else
3)
else
(if i.val < 963 then
3
else
3))
else
(if i.val < 966 then
(if i.val < 965 then
3
else
3)
else
(if i.val < 967 then
3
else
3)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
3
else
3)
else
(if i.val < 971 then
3
else
3))
else
(if i.val < 974 then
(if i.val < 973 then
3
else
3)
else
(if i.val < 975 then
3
else
3))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
3
else
3)
else
(if i.val < 979 then
3
else
3))
else
(if i.val < 982 then
(if i.val < 981 then
3
else
3)
else
(if i.val < 983 then
3
else
3)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
3
else
3)
else
(if i.val < 987 then
3
else
3))
else
(if i.val < 990 then
(if i.val < 989 then
3
else
3)
else
(if i.val < 991 then
3
else
3)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
3
else
3)
else
(if i.val < 995 then
3
else
3))
else
(if i.val < 998 then
(if i.val < 997 then
3
else
3)
else
(if i.val < 999 then
3
else
3)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
3
else
3)
else
(if i.val < 1003 then
3
else
3))
else
(if i.val < 1006 then
(if i.val < 1005 then
3
else
3)
else
(if i.val < 1007 then
3
else
3))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
3
else
3)
else
(if i.val < 1011 then
3
else
3))
else
(if i.val < 1014 then
(if i.val < 1013 then
3
else
3)
else
(if i.val < 1015 then
3
else
3)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
3
else
3)
else
(if i.val < 1019 then
3
else
3))
else
(if i.val < 1022 then
(if i.val < 1021 then
3
else
3)
else
(if i.val < 1023 then
3
else
3)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths1Part0002 : Fin 2880 → ℕ :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
3
else
3)
else
(if i.val < 1027 then
3
else
3))
else
(if i.val < 1030 then
(if i.val < 1029 then
3
else
3)
else
(if i.val < 1031 then
3
else
3)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
3
else
3)
else
(if i.val < 1035 then
3
else
3))
else
(if i.val < 1038 then
(if i.val < 1037 then
3
else
3)
else
(if i.val < 1039 then
3
else
3))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
3
else
3)
else
(if i.val < 1043 then
3
else
3))
else
(if i.val < 1046 then
(if i.val < 1045 then
3
else
3)
else
(if i.val < 1047 then
3
else
3)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
3
else
3)
else
(if i.val < 1051 then
3
else
3))
else
(if i.val < 1054 then
(if i.val < 1053 then
3
else
3)
else
(if i.val < 1055 then
3
else
3)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
3
else
3)
else
(if i.val < 1059 then
3
else
3))
else
(if i.val < 1062 then
(if i.val < 1061 then
3
else
3)
else
(if i.val < 1063 then
3
else
3)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
3
else
3)
else
(if i.val < 1067 then
3
else
3))
else
(if i.val < 1070 then
(if i.val < 1069 then
3
else
3)
else
(if i.val < 1071 then
3
else
3))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
3
else
3)
else
(if i.val < 1075 then
3
else
3))
else
(if i.val < 1078 then
(if i.val < 1077 then
3
else
3)
else
(if i.val < 1079 then
3
else
3)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
3
else
3)
else
(if i.val < 1083 then
3
else
3))
else
(if i.val < 1086 then
(if i.val < 1085 then
3
else
3)
else
(if i.val < 1087 then
3
else
3))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
3
else
3)
else
(if i.val < 1091 then
3
else
3))
else
(if i.val < 1094 then
(if i.val < 1093 then
3
else
3)
else
(if i.val < 1095 then
3
else
3)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
3
else
3)
else
(if i.val < 1099 then
3
else
3))
else
(if i.val < 1102 then
(if i.val < 1101 then
3
else
3)
else
(if i.val < 1103 then
3
else
3))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
3
else
3)
else
(if i.val < 1107 then
3
else
3))
else
(if i.val < 1110 then
(if i.val < 1109 then
3
else
3)
else
(if i.val < 1111 then
3
else
3)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
3
else
3)
else
(if i.val < 1115 then
3
else
3))
else
(if i.val < 1118 then
(if i.val < 1117 then
3
else
3)
else
(if i.val < 1119 then
3
else
3)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
3
else
3)
else
(if i.val < 1123 then
3
else
3))
else
(if i.val < 1126 then
(if i.val < 1125 then
3
else
3)
else
(if i.val < 1127 then
3
else
3)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
3
else
3)
else
(if i.val < 1131 then
3
else
3))
else
(if i.val < 1134 then
(if i.val < 1133 then
3
else
3)
else
(if i.val < 1135 then
3
else
3))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
3
else
3)
else
(if i.val < 1139 then
3
else
3))
else
(if i.val < 1142 then
(if i.val < 1141 then
3
else
3)
else
(if i.val < 1143 then
3
else
3)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
3
else
3)
else
(if i.val < 1147 then
3
else
3))
else
(if i.val < 1150 then
(if i.val < 1149 then
3
else
3)
else
(if i.val < 1151 then
3
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
3
else
3)
else
(if i.val < 1155 then
3
else
3))
else
(if i.val < 1158 then
(if i.val < 1157 then
3
else
3)
else
(if i.val < 1159 then
3
else
3)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
3
else
3)
else
(if i.val < 1163 then
3
else
3))
else
(if i.val < 1166 then
(if i.val < 1165 then
3
else
3)
else
(if i.val < 1167 then
3
else
3))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
3
else
3)
else
(if i.val < 1171 then
3
else
3))
else
(if i.val < 1174 then
(if i.val < 1173 then
3
else
3)
else
(if i.val < 1175 then
3
else
3)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
3
else
3)
else
(if i.val < 1179 then
3
else
3))
else
(if i.val < 1182 then
(if i.val < 1181 then
3
else
3)
else
(if i.val < 1183 then
3
else
3)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
3
else
3)
else
(if i.val < 1187 then
3
else
3))
else
(if i.val < 1190 then
(if i.val < 1189 then
3
else
3)
else
(if i.val < 1191 then
3
else
3)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
3
else
3)
else
(if i.val < 1195 then
3
else
3))
else
(if i.val < 1198 then
(if i.val < 1197 then
3
else
3)
else
(if i.val < 1199 then
3
else
3))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
3
else
3)
else
(if i.val < 1203 then
3
else
3))
else
(if i.val < 1206 then
(if i.val < 1205 then
3
else
3)
else
(if i.val < 1207 then
3
else
3)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
3
else
3)
else
(if i.val < 1211 then
3
else
3))
else
(if i.val < 1214 then
(if i.val < 1213 then
3
else
3)
else
(if i.val < 1215 then
3
else
3))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
3
else
3)
else
(if i.val < 1219 then
3
else
3))
else
(if i.val < 1222 then
(if i.val < 1221 then
3
else
3)
else
(if i.val < 1223 then
3
else
3)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
3
else
3)
else
(if i.val < 1227 then
3
else
3))
else
(if i.val < 1230 then
(if i.val < 1229 then
3
else
3)
else
(if i.val < 1231 then
3
else
3))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
3
else
3)
else
(if i.val < 1235 then
3
else
3))
else
(if i.val < 1238 then
(if i.val < 1237 then
3
else
3)
else
(if i.val < 1239 then
3
else
3)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
3
else
3)
else
(if i.val < 1243 then
3
else
3))
else
(if i.val < 1246 then
(if i.val < 1245 then
3
else
3)
else
(if i.val < 1247 then
3
else
3)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
3
else
3)
else
(if i.val < 1251 then
3
else
3))
else
(if i.val < 1254 then
(if i.val < 1253 then
3
else
3)
else
(if i.val < 1255 then
3
else
3)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
3
else
3)
else
(if i.val < 1259 then
3
else
3))
else
(if i.val < 1262 then
(if i.val < 1261 then
3
else
3)
else
(if i.val < 1263 then
3
else
3))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
3
else
3)
else
(if i.val < 1267 then
3
else
3))
else
(if i.val < 1270 then
(if i.val < 1269 then
3
else
3)
else
(if i.val < 1271 then
3
else
3)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
3
else
3)
else
(if i.val < 1275 then
3
else
3))
else
(if i.val < 1278 then
(if i.val < 1277 then
3
else
3)
else
(if i.val < 1279 then
3
else
3))))))))
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
3
else
3))
else
(if i.val < 1286 then
(if i.val < 1285 then
3
else
3)
else
(if i.val < 1287 then
3
else
3)))
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
3
else
3)
else
(if i.val < 1295 then
3
else
3))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
3
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
3
else
3)
else
(if i.val < 1303 then
3
else
3)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
3
else
3)
else
(if i.val < 1307 then
3
else
3))
else
(if i.val < 1310 then
(if i.val < 1309 then
3
else
3)
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
3)
else
(if i.val < 1315 then
3
else
3))
else
(if i.val < 1318 then
(if i.val < 1317 then
3
else
3)
else
(if i.val < 1319 then
3
else
3)))
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
3))
else
(if i.val < 1326 then
(if i.val < 1325 then
3
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
3
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
3)
else
(if i.val < 1339 then
3
else
3))
else
(if i.val < 1342 then
(if i.val < 1341 then
3
else
3)
else
(if i.val < 1343 then
3
else
3))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
3
else
3)
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
3
else
3)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
3
else
3)
else
(if i.val < 1355 then
3
else
3))
else
(if i.val < 1358 then
(if i.val < 1357 then
3
else
3)
else
(if i.val < 1359 then
3
else
3))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
3
else
3)
else
(if i.val < 1363 then
3
else
3))
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
3)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
3
else
3)
else
(if i.val < 1371 then
3
else
3))
else
(if i.val < 1374 then
(if i.val < 1373 then
3
else
3)
else
(if i.val < 1375 then
3
else
3)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
3
else
3)
else
(if i.val < 1379 then
3
else
3))
else
(if i.val < 1382 then
(if i.val < 1381 then
3
else
3)
else
(if i.val < 1383 then
3
else
3)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
3
else
3)
else
(if i.val < 1387 then
3
else
3))
else
(if i.val < 1390 then
(if i.val < 1389 then
3
else
3)
else
(if i.val < 1391 then
3
else
3))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
3
else
3)
else
(if i.val < 1395 then
3
else
3))
else
(if i.val < 1398 then
(if i.val < 1397 then
3
else
3)
else
(if i.val < 1399 then
3
else
3)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
3
else
3)
else
(if i.val < 1403 then
3
else
3))
else
(if i.val < 1406 then
(if i.val < 1405 then
3
else
3)
else
(if i.val < 1407 then
3
else
3)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
3
else
3)
else
(if i.val < 1411 then
3
else
3))
else
(if i.val < 1414 then
(if i.val < 1413 then
3
else
3)
else
(if i.val < 1415 then
3
else
3)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
3
else
3)
else
(if i.val < 1419 then
3
else
3))
else
(if i.val < 1422 then
(if i.val < 1421 then
3
else
3)
else
(if i.val < 1423 then
3
else
3))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
3
else
3)
else
(if i.val < 1427 then
3
else
3))
else
(if i.val < 1430 then
(if i.val < 1429 then
3
else
3)
else
(if i.val < 1431 then
3
else
3)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
3
else
3)
else
(if i.val < 1435 then
3
else
3))
else
(if i.val < 1438 then
(if i.val < 1437 then
3
else
3)
else
(if i.val < 1439 then
3
else
3)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
3
else
3)
else
(if i.val < 1443 then
3
else
3))
else
(if i.val < 1446 then
(if i.val < 1445 then
3
else
3)
else
(if i.val < 1447 then
3
else
3)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
3
else
3)
else
(if i.val < 1451 then
3
else
3))
else
(if i.val < 1454 then
(if i.val < 1453 then
3
else
3)
else
(if i.val < 1455 then
3
else
3))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
3
else
3)
else
(if i.val < 1459 then
3
else
3))
else
(if i.val < 1462 then
(if i.val < 1461 then
3
else
3)
else
(if i.val < 1463 then
3
else
3)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
3
else
3)
else
(if i.val < 1467 then
3
else
3))
else
(if i.val < 1470 then
(if i.val < 1469 then
3
else
3)
else
(if i.val < 1471 then
3
else
3))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
3
else
3)
else
(if i.val < 1475 then
3
else
3))
else
(if i.val < 1478 then
(if i.val < 1477 then
3
else
3)
else
(if i.val < 1479 then
3
else
3)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
3
else
3)
else
(if i.val < 1483 then
3
else
3))
else
(if i.val < 1486 then
(if i.val < 1485 then
3
else
3)
else
(if i.val < 1487 then
3
else
3))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
3
else
3)
else
(if i.val < 1491 then
3
else
3))
else
(if i.val < 1494 then
(if i.val < 1493 then
3
else
3)
else
(if i.val < 1495 then
3
else
3)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
3
else
3)
else
(if i.val < 1499 then
3
else
3))
else
(if i.val < 1502 then
(if i.val < 1501 then
3
else
3)
else
(if i.val < 1503 then
3
else
3)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
3
else
3)
else
(if i.val < 1507 then
3
else
3))
else
(if i.val < 1510 then
(if i.val < 1509 then
3
else
3)
else
(if i.val < 1511 then
3
else
3)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
3
else
3)
else
(if i.val < 1515 then
3
else
3))
else
(if i.val < 1518 then
(if i.val < 1517 then
3
else
3)
else
(if i.val < 1519 then
3
else
3))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
3
else
3)
else
(if i.val < 1523 then
3
else
3))
else
(if i.val < 1526 then
(if i.val < 1525 then
3
else
3)
else
(if i.val < 1527 then
3
else
3)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
3
else
3)
else
(if i.val < 1531 then
3
else
3))
else
(if i.val < 1534 then
(if i.val < 1533 then
3
else
3)
else
(if i.val < 1535 then
3
else
3)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths1Part0003 : Fin 2880 → ℕ :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
3
else
3)
else
(if i.val < 1539 then
3
else
3))
else
(if i.val < 1542 then
(if i.val < 1541 then
3
else
3)
else
(if i.val < 1543 then
3
else
3)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
3
else
3)
else
(if i.val < 1547 then
3
else
3))
else
(if i.val < 1550 then
(if i.val < 1549 then
3
else
3)
else
(if i.val < 1551 then
3
else
3))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
3
else
3)
else
(if i.val < 1555 then
3
else
3))
else
(if i.val < 1558 then
(if i.val < 1557 then
3
else
3)
else
(if i.val < 1559 then
3
else
3)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
3
else
3)
else
(if i.val < 1563 then
3
else
3))
else
(if i.val < 1566 then
(if i.val < 1565 then
3
else
3)
else
(if i.val < 1567 then
3
else
3)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
3
else
3)
else
(if i.val < 1571 then
3
else
3))
else
(if i.val < 1574 then
(if i.val < 1573 then
3
else
3)
else
(if i.val < 1575 then
3
else
3)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
3
else
3)
else
(if i.val < 1579 then
3
else
3))
else
(if i.val < 1582 then
(if i.val < 1581 then
3
else
3)
else
(if i.val < 1583 then
3
else
3))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
3
else
3)
else
(if i.val < 1587 then
3
else
3))
else
(if i.val < 1590 then
(if i.val < 1589 then
3
else
3)
else
(if i.val < 1591 then
3
else
3)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
3
else
3)
else
(if i.val < 1595 then
3
else
3))
else
(if i.val < 1598 then
(if i.val < 1597 then
3
else
3)
else
(if i.val < 1599 then
3
else
3))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
3
else
3)
else
(if i.val < 1603 then
3
else
3))
else
(if i.val < 1606 then
(if i.val < 1605 then
3
else
3)
else
(if i.val < 1607 then
3
else
3)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
3
else
3)
else
(if i.val < 1611 then
3
else
3))
else
(if i.val < 1614 then
(if i.val < 1613 then
3
else
3)
else
(if i.val < 1615 then
3
else
3))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
3
else
3)
else
(if i.val < 1619 then
3
else
3))
else
(if i.val < 1622 then
(if i.val < 1621 then
3
else
3)
else
(if i.val < 1623 then
3
else
3)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
3
else
3)
else
(if i.val < 1627 then
3
else
3))
else
(if i.val < 1630 then
(if i.val < 1629 then
3
else
3)
else
(if i.val < 1631 then
3
else
3)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
3
else
3)
else
(if i.val < 1635 then
3
else
3))
else
(if i.val < 1638 then
(if i.val < 1637 then
3
else
3)
else
(if i.val < 1639 then
3
else
3)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
3
else
3)
else
(if i.val < 1643 then
3
else
3))
else
(if i.val < 1646 then
(if i.val < 1645 then
3
else
3)
else
(if i.val < 1647 then
3
else
3))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
3
else
3)
else
(if i.val < 1651 then
3
else
3))
else
(if i.val < 1654 then
(if i.val < 1653 then
3
else
3)
else
(if i.val < 1655 then
3
else
3)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
3
else
3)
else
(if i.val < 1659 then
3
else
3))
else
(if i.val < 1662 then
(if i.val < 1661 then
3
else
3)
else
(if i.val < 1663 then
3
else
3)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
3
else
3)
else
(if i.val < 1667 then
3
else
3))
else
(if i.val < 1670 then
(if i.val < 1669 then
3
else
3)
else
(if i.val < 1671 then
3
else
3)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
3
else
3)
else
(if i.val < 1675 then
3
else
3))
else
(if i.val < 1678 then
(if i.val < 1677 then
3
else
3)
else
(if i.val < 1679 then
3
else
3))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
3
else
3)
else
(if i.val < 1683 then
3
else
3))
else
(if i.val < 1686 then
(if i.val < 1685 then
3
else
3)
else
(if i.val < 1687 then
3
else
3)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
3
else
3)
else
(if i.val < 1691 then
3
else
3))
else
(if i.val < 1694 then
(if i.val < 1693 then
3
else
3)
else
(if i.val < 1695 then
3
else
3)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
3
else
3)
else
(if i.val < 1699 then
3
else
3))
else
(if i.val < 1702 then
(if i.val < 1701 then
3
else
3)
else
(if i.val < 1703 then
3
else
3)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
3
else
3)
else
(if i.val < 1707 then
3
else
3))
else
(if i.val < 1710 then
(if i.val < 1709 then
3
else
3)
else
(if i.val < 1711 then
3
else
3))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
3
else
3)
else
(if i.val < 1715 then
3
else
3))
else
(if i.val < 1718 then
(if i.val < 1717 then
3
else
3)
else
(if i.val < 1719 then
3
else
3)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
3
else
3)
else
(if i.val < 1723 then
3
else
3))
else
(if i.val < 1726 then
(if i.val < 1725 then
3
else
3)
else
(if i.val < 1727 then
3
else
3))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
3
else
3)
else
(if i.val < 1731 then
3
else
3))
else
(if i.val < 1734 then
(if i.val < 1733 then
3
else
3)
else
(if i.val < 1735 then
3
else
3)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
3
else
3)
else
(if i.val < 1739 then
3
else
3))
else
(if i.val < 1742 then
(if i.val < 1741 then
3
else
3)
else
(if i.val < 1743 then
3
else
3))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
3
else
3)
else
(if i.val < 1747 then
3
else
3))
else
(if i.val < 1750 then
(if i.val < 1749 then
3
else
3)
else
(if i.val < 1751 then
3
else
3)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
3
else
3)
else
(if i.val < 1755 then
3
else
3))
else
(if i.val < 1758 then
(if i.val < 1757 then
3
else
3)
else
(if i.val < 1759 then
3
else
3)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
3
else
3)
else
(if i.val < 1763 then
3
else
3))
else
(if i.val < 1766 then
(if i.val < 1765 then
3
else
3)
else
(if i.val < 1767 then
3
else
3)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
3
else
3)
else
(if i.val < 1771 then
3
else
3))
else
(if i.val < 1774 then
(if i.val < 1773 then
3
else
3)
else
(if i.val < 1775 then
3
else
3))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
3
else
3)
else
(if i.val < 1779 then
3
else
3))
else
(if i.val < 1782 then
(if i.val < 1781 then
3
else
3)
else
(if i.val < 1783 then
3
else
3)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
3
else
3)
else
(if i.val < 1787 then
3
else
3))
else
(if i.val < 1790 then
(if i.val < 1789 then
3
else
3)
else
(if i.val < 1791 then
3
else
3))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
3
else
3)
else
(if i.val < 1795 then
3
else
3))
else
(if i.val < 1798 then
(if i.val < 1797 then
3
else
3)
else
(if i.val < 1799 then
3
else
3)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
3
else
3)
else
(if i.val < 1803 then
3
else
3))
else
(if i.val < 1806 then
(if i.val < 1805 then
3
else
3)
else
(if i.val < 1807 then
3
else
3))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
3
else
3)
else
(if i.val < 1811 then
3
else
3))
else
(if i.val < 1814 then
(if i.val < 1813 then
3
else
3)
else
(if i.val < 1815 then
3
else
3)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
3
else
3)
else
(if i.val < 1819 then
3
else
3))
else
(if i.val < 1822 then
(if i.val < 1821 then
3
else
3)
else
(if i.val < 1823 then
3
else
3)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
3
else
3)
else
(if i.val < 1827 then
3
else
3))
else
(if i.val < 1830 then
(if i.val < 1829 then
3
else
3)
else
(if i.val < 1831 then
3
else
3)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
3
else
3)
else
(if i.val < 1835 then
3
else
3))
else
(if i.val < 1838 then
(if i.val < 1837 then
3
else
3)
else
(if i.val < 1839 then
3
else
3))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
3
else
3)
else
(if i.val < 1843 then
3
else
3))
else
(if i.val < 1846 then
(if i.val < 1845 then
3
else
3)
else
(if i.val < 1847 then
3
else
3)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
3
else
3)
else
(if i.val < 1851 then
3
else
3))
else
(if i.val < 1854 then
(if i.val < 1853 then
3
else
3)
else
(if i.val < 1855 then
3
else
3))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
3
else
3)
else
(if i.val < 1859 then
3
else
3))
else
(if i.val < 1862 then
(if i.val < 1861 then
3
else
3)
else
(if i.val < 1863 then
3
else
3)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
3
else
3)
else
(if i.val < 1867 then
3
else
3))
else
(if i.val < 1870 then
(if i.val < 1869 then
3
else
3)
else
(if i.val < 1871 then
3
else
3))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
3
else
3)
else
(if i.val < 1875 then
3
else
3))
else
(if i.val < 1878 then
(if i.val < 1877 then
3
else
3)
else
(if i.val < 1879 then
3
else
3)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
3
else
3)
else
(if i.val < 1883 then
3
else
3))
else
(if i.val < 1886 then
(if i.val < 1885 then
3
else
3)
else
(if i.val < 1887 then
3
else
3)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
3
else
3)
else
(if i.val < 1891 then
3
else
3))
else
(if i.val < 1894 then
(if i.val < 1893 then
3
else
3)
else
(if i.val < 1895 then
3
else
3)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
3
else
3)
else
(if i.val < 1899 then
3
else
3))
else
(if i.val < 1902 then
(if i.val < 1901 then
3
else
3)
else
(if i.val < 1903 then
3
else
3))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
3
else
3)
else
(if i.val < 1907 then
3
else
3))
else
(if i.val < 1910 then
(if i.val < 1909 then
3
else
3)
else
(if i.val < 1911 then
3
else
3)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
3
else
3)
else
(if i.val < 1915 then
3
else
3))
else
(if i.val < 1918 then
(if i.val < 1917 then
3
else
3)
else
(if i.val < 1919 then
3
else
3)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
3
else
3)
else
(if i.val < 1923 then
3
else
3))
else
(if i.val < 1926 then
(if i.val < 1925 then
3
else
3)
else
(if i.val < 1927 then
3
else
3)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
3
else
3)
else
(if i.val < 1931 then
3
else
3))
else
(if i.val < 1934 then
(if i.val < 1933 then
3
else
3)
else
(if i.val < 1935 then
3
else
3))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
3
else
3)
else
(if i.val < 1939 then
3
else
3))
else
(if i.val < 1942 then
(if i.val < 1941 then
3
else
3)
else
(if i.val < 1943 then
3
else
3)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
3
else
3)
else
(if i.val < 1947 then
3
else
3))
else
(if i.val < 1950 then
(if i.val < 1949 then
3
else
3)
else
(if i.val < 1951 then
3
else
3)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
3
else
3)
else
(if i.val < 1955 then
3
else
3))
else
(if i.val < 1958 then
(if i.val < 1957 then
3
else
3)
else
(if i.val < 1959 then
3
else
3)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
3
else
3)
else
(if i.val < 1963 then
3
else
3))
else
(if i.val < 1966 then
(if i.val < 1965 then
3
else
3)
else
(if i.val < 1967 then
3
else
3))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
3
else
3)
else
(if i.val < 1971 then
3
else
3))
else
(if i.val < 1974 then
(if i.val < 1973 then
3
else
3)
else
(if i.val < 1975 then
3
else
3)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
3
else
3)
else
(if i.val < 1979 then
3
else
3))
else
(if i.val < 1982 then
(if i.val < 1981 then
3
else
3)
else
(if i.val < 1983 then
3
else
3))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
3
else
3)
else
(if i.val < 1987 then
3
else
3))
else
(if i.val < 1990 then
(if i.val < 1989 then
3
else
3)
else
(if i.val < 1991 then
3
else
3)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
3
else
3)
else
(if i.val < 1995 then
3
else
3))
else
(if i.val < 1998 then
(if i.val < 1997 then
3
else
3)
else
(if i.val < 1999 then
3
else
3))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
3
else
3)
else
(if i.val < 2003 then
3
else
3))
else
(if i.val < 2006 then
(if i.val < 2005 then
3
else
3)
else
(if i.val < 2007 then
3
else
3)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
3
else
3)
else
(if i.val < 2011 then
3
else
3))
else
(if i.val < 2014 then
(if i.val < 2013 then
3
else
3)
else
(if i.val < 2015 then
3
else
3)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
3
else
3)
else
(if i.val < 2019 then
3
else
3))
else
(if i.val < 2022 then
(if i.val < 2021 then
3
else
3)
else
(if i.val < 2023 then
3
else
3)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
3
else
3)
else
(if i.val < 2027 then
3
else
3))
else
(if i.val < 2030 then
(if i.val < 2029 then
3
else
3)
else
(if i.val < 2031 then
3
else
3))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
3
else
3)
else
(if i.val < 2035 then
3
else
3))
else
(if i.val < 2038 then
(if i.val < 2037 then
3
else
3)
else
(if i.val < 2039 then
3
else
3)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
3
else
3)
else
(if i.val < 2043 then
3
else
3))
else
(if i.val < 2046 then
(if i.val < 2045 then
3
else
3)
else
(if i.val < 2047 then
3
else
3)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths1Part0004 : Fin 2880 → ℕ :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
3
else
3)
else
(if i.val < 2051 then
3
else
3))
else
(if i.val < 2054 then
(if i.val < 2053 then
3
else
3)
else
(if i.val < 2055 then
3
else
3)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
3
else
3)
else
(if i.val < 2059 then
3
else
3))
else
(if i.val < 2062 then
(if i.val < 2061 then
3
else
3)
else
(if i.val < 2063 then
3
else
3))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
3
else
3)
else
(if i.val < 2067 then
3
else
3))
else
(if i.val < 2070 then
(if i.val < 2069 then
3
else
3)
else
(if i.val < 2071 then
3
else
3)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
3
else
3)
else
(if i.val < 2075 then
3
else
3))
else
(if i.val < 2078 then
(if i.val < 2077 then
3
else
3)
else
(if i.val < 2079 then
3
else
3)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
3
else
3)
else
(if i.val < 2083 then
3
else
3))
else
(if i.val < 2086 then
(if i.val < 2085 then
3
else
3)
else
(if i.val < 2087 then
3
else
3)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
3
else
3)
else
(if i.val < 2091 then
3
else
3))
else
(if i.val < 2094 then
(if i.val < 2093 then
3
else
3)
else
(if i.val < 2095 then
3
else
3))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
3
else
3)
else
(if i.val < 2099 then
3
else
3))
else
(if i.val < 2102 then
(if i.val < 2101 then
3
else
3)
else
(if i.val < 2103 then
3
else
3)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
3
else
3)
else
(if i.val < 2107 then
3
else
3))
else
(if i.val < 2110 then
(if i.val < 2109 then
3
else
3)
else
(if i.val < 2111 then
3
else
3))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
3
else
3)
else
(if i.val < 2115 then
3
else
3))
else
(if i.val < 2118 then
(if i.val < 2117 then
3
else
3)
else
(if i.val < 2119 then
3
else
3)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
3
else
3)
else
(if i.val < 2123 then
3
else
3))
else
(if i.val < 2126 then
(if i.val < 2125 then
3
else
3)
else
(if i.val < 2127 then
3
else
3))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
3
else
3)
else
(if i.val < 2131 then
3
else
3))
else
(if i.val < 2134 then
(if i.val < 2133 then
3
else
3)
else
(if i.val < 2135 then
3
else
3)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
3
else
3)
else
(if i.val < 2139 then
3
else
3))
else
(if i.val < 2142 then
(if i.val < 2141 then
3
else
3)
else
(if i.val < 2143 then
3
else
3)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
3
else
3)
else
(if i.val < 2147 then
3
else
3))
else
(if i.val < 2150 then
(if i.val < 2149 then
3
else
3)
else
(if i.val < 2151 then
3
else
3)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
3
else
3)
else
(if i.val < 2155 then
3
else
3))
else
(if i.val < 2158 then
(if i.val < 2157 then
3
else
3)
else
(if i.val < 2159 then
3
else
3))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
3
else
3)
else
(if i.val < 2163 then
3
else
3))
else
(if i.val < 2166 then
(if i.val < 2165 then
3
else
3)
else
(if i.val < 2167 then
3
else
3)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
3
else
3)
else
(if i.val < 2171 then
3
else
3))
else
(if i.val < 2174 then
(if i.val < 2173 then
3
else
3)
else
(if i.val < 2175 then
3
else
3)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
3
else
3)
else
(if i.val < 2179 then
3
else
3))
else
(if i.val < 2182 then
(if i.val < 2181 then
3
else
3)
else
(if i.val < 2183 then
3
else
3)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
3
else
3)
else
(if i.val < 2187 then
3
else
3))
else
(if i.val < 2190 then
(if i.val < 2189 then
3
else
3)
else
(if i.val < 2191 then
3
else
3))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
3
else
3)
else
(if i.val < 2195 then
3
else
3))
else
(if i.val < 2198 then
(if i.val < 2197 then
3
else
3)
else
(if i.val < 2199 then
3
else
3)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
3
else
3)
else
(if i.val < 2203 then
3
else
3))
else
(if i.val < 2206 then
(if i.val < 2205 then
3
else
3)
else
(if i.val < 2207 then
3
else
3)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
3
else
3)
else
(if i.val < 2211 then
3
else
3))
else
(if i.val < 2214 then
(if i.val < 2213 then
3
else
3)
else
(if i.val < 2215 then
3
else
3)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
3
else
3)
else
(if i.val < 2219 then
3
else
3))
else
(if i.val < 2222 then
(if i.val < 2221 then
3
else
3)
else
(if i.val < 2223 then
3
else
3))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
3
else
3)
else
(if i.val < 2227 then
3
else
3))
else
(if i.val < 2230 then
(if i.val < 2229 then
3
else
3)
else
(if i.val < 2231 then
3
else
3)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
3
else
3)
else
(if i.val < 2235 then
3
else
3))
else
(if i.val < 2238 then
(if i.val < 2237 then
3
else
3)
else
(if i.val < 2239 then
3
else
3))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
3
else
3)
else
(if i.val < 2243 then
3
else
3))
else
(if i.val < 2246 then
(if i.val < 2245 then
3
else
3)
else
(if i.val < 2247 then
3
else
3)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
3
else
3)
else
(if i.val < 2251 then
3
else
3))
else
(if i.val < 2254 then
(if i.val < 2253 then
3
else
3)
else
(if i.val < 2255 then
3
else
3))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
3
else
3)
else
(if i.val < 2259 then
3
else
3))
else
(if i.val < 2262 then
(if i.val < 2261 then
3
else
3)
else
(if i.val < 2263 then
3
else
3)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
3
else
3)
else
(if i.val < 2267 then
3
else
3))
else
(if i.val < 2270 then
(if i.val < 2269 then
3
else
3)
else
(if i.val < 2271 then
3
else
3)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
3
else
3)
else
(if i.val < 2275 then
3
else
3))
else
(if i.val < 2278 then
(if i.val < 2277 then
3
else
3)
else
(if i.val < 2279 then
3
else
3)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
3
else
3)
else
(if i.val < 2283 then
3
else
3))
else
(if i.val < 2286 then
(if i.val < 2285 then
3
else
3)
else
(if i.val < 2287 then
3
else
3))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
3
else
3)
else
(if i.val < 2291 then
3
else
3))
else
(if i.val < 2294 then
(if i.val < 2293 then
3
else
3)
else
(if i.val < 2295 then
3
else
3)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
3
else
3)
else
(if i.val < 2299 then
3
else
3))
else
(if i.val < 2302 then
(if i.val < 2301 then
3
else
3)
else
(if i.val < 2303 then
3
else
3))))))))
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
3)
else
(if i.val < 2307 then
3
else
3))
else
(if i.val < 2310 then
(if i.val < 2309 then
3
else
3)
else
(if i.val < 2311 then
3
else
3)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
3
else
3)
else
(if i.val < 2315 then
3
else
3))
else
(if i.val < 2318 then
(if i.val < 2317 then
3
else
3)
else
(if i.val < 2319 then
3
else
3))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
3
else
3)
else
(if i.val < 2323 then
3
else
3))
else
(if i.val < 2326 then
(if i.val < 2325 then
3
else
3)
else
(if i.val < 2327 then
3
else
3)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
3
else
3)
else
(if i.val < 2331 then
3
else
3))
else
(if i.val < 2334 then
(if i.val < 2333 then
3
else
3)
else
(if i.val < 2335 then
3
else
3)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
3
else
3)
else
(if i.val < 2339 then
3
else
3))
else
(if i.val < 2342 then
(if i.val < 2341 then
3
else
3)
else
(if i.val < 2343 then
3
else
3)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
3
else
3)
else
(if i.val < 2347 then
3
else
3))
else
(if i.val < 2350 then
(if i.val < 2349 then
3
else
3)
else
(if i.val < 2351 then
3
else
3))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
3
else
3)
else
(if i.val < 2355 then
3
else
3))
else
(if i.val < 2358 then
(if i.val < 2357 then
3
else
3)
else
(if i.val < 2359 then
3
else
3)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
3
else
3)
else
(if i.val < 2363 then
3
else
3))
else
(if i.val < 2366 then
(if i.val < 2365 then
3
else
3)
else
(if i.val < 2367 then
3
else
3))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
3
else
3)
else
(if i.val < 2371 then
3
else
3))
else
(if i.val < 2374 then
(if i.val < 2373 then
3
else
3)
else
(if i.val < 2375 then
3
else
3)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
3
else
3)
else
(if i.val < 2379 then
3
else
3))
else
(if i.val < 2382 then
(if i.val < 2381 then
3
else
3)
else
(if i.val < 2383 then
3
else
3))))
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
3
else
3))
else
(if i.val < 2390 then
(if i.val < 2389 then
3
else
3)
else
(if i.val < 2391 then
3
else
3)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
3
else
3)
else
(if i.val < 2395 then
3
else
3))
else
(if i.val < 2398 then
(if i.val < 2397 then
3
else
3)
else
(if i.val < 2399 then
3
else
3)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
3
else
3)
else
(if i.val < 2403 then
3
else
3))
else
(if i.val < 2406 then
(if i.val < 2405 then
3
else
3)
else
(if i.val < 2407 then
3
else
3)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
3
else
3)
else
(if i.val < 2411 then
3
else
3))
else
(if i.val < 2414 then
(if i.val < 2413 then
3
else
3)
else
(if i.val < 2415 then
3
else
3))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
3
else
3)
else
(if i.val < 2419 then
3
else
3))
else
(if i.val < 2422 then
(if i.val < 2421 then
3
else
3)
else
(if i.val < 2423 then
3
else
3)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
3
else
3)
else
(if i.val < 2427 then
3
else
3))
else
(if i.val < 2430 then
(if i.val < 2429 then
3
else
3)
else
(if i.val < 2431 then
3
else
3)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
3
else
3)
else
(if i.val < 2435 then
3
else
3))
else
(if i.val < 2438 then
(if i.val < 2437 then
3
else
3)
else
(if i.val < 2439 then
3
else
3)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
3
else
3)
else
(if i.val < 2443 then
3
else
3))
else
(if i.val < 2446 then
(if i.val < 2445 then
3
else
3)
else
(if i.val < 2447 then
3
else
3))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
3
else
3)
else
(if i.val < 2451 then
3
else
3))
else
(if i.val < 2454 then
(if i.val < 2453 then
3
else
3)
else
(if i.val < 2455 then
3
else
3)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
3
else
3)
else
(if i.val < 2459 then
3
else
3))
else
(if i.val < 2462 then
(if i.val < 2461 then
3
else
3)
else
(if i.val < 2463 then
3
else
3)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
3
else
3)
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
3
else
3)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
3
else
3)
else
(if i.val < 2475 then
3
else
3))
else
(if i.val < 2478 then
(if i.val < 2477 then
3
else
3)
else
(if i.val < 2479 then
3
else
3))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
3
else
3)
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
3)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
3
else
3)
else
(if i.val < 2491 then
3
else
3))
else
(if i.val < 2494 then
(if i.val < 2493 then
3
else
3)
else
(if i.val < 2495 then
3
else
3))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
3
else
3)
else
(if i.val < 2499 then
3
else
3))
else
(if i.val < 2502 then
(if i.val < 2501 then
3
else
3)
else
(if i.val < 2503 then
3
else
3)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
3
else
3)
else
(if i.val < 2507 then
3
else
3))
else
(if i.val < 2510 then
(if i.val < 2509 then
3
else
3)
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
3
else
3)
else
(if i.val < 2515 then
3
else
3))
else
(if i.val < 2518 then
(if i.val < 2517 then
3
else
3)
else
(if i.val < 2519 then
3
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
3))
else
(if i.val < 2526 then
(if i.val < 2525 then
3
else
3)
else
(if i.val < 2527 then
3
else
3)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
3
else
3)
else
(if i.val < 2531 then
3
else
3))
else
(if i.val < 2534 then
(if i.val < 2533 then
3
else
3)
else
(if i.val < 2535 then
3
else
3)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
3
else
3)
else
(if i.val < 2539 then
3
else
3))
else
(if i.val < 2542 then
(if i.val < 2541 then
3
else
3)
else
(if i.val < 2543 then
3
else
3))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
3
else
3)
else
(if i.val < 2547 then
3
else
3))
else
(if i.val < 2550 then
(if i.val < 2549 then
3
else
3)
else
(if i.val < 2551 then
3
else
3)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
3
else
3)
else
(if i.val < 2555 then
3
else
3))
else
(if i.val < 2558 then
(if i.val < 2557 then
3
else
3)
else
(if i.val < 2559 then
3
else
3)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths1Part0005 : Fin 2880 → ℕ :=
  fun i => (if i.val < 2720 then
(if i.val < 2640 then
(if i.val < 2600 then
(if i.val < 2580 then
(if i.val < 2570 then
(if i.val < 2565 then
(if i.val < 2562 then
(if i.val < 2561 then
3
else
3)
else
(if i.val < 2563 then
3
else
(if i.val < 2564 then
3
else
3)))
else
(if i.val < 2567 then
(if i.val < 2566 then
3
else
3)
else
(if i.val < 2568 then
3
else
(if i.val < 2569 then
3
else
3))))
else
(if i.val < 2575 then
(if i.val < 2572 then
(if i.val < 2571 then
3
else
3)
else
(if i.val < 2573 then
3
else
(if i.val < 2574 then
3
else
3)))
else
(if i.val < 2577 then
(if i.val < 2576 then
3
else
3)
else
(if i.val < 2578 then
3
else
(if i.val < 2579 then
3
else
3)))))
else
(if i.val < 2590 then
(if i.val < 2585 then
(if i.val < 2582 then
(if i.val < 2581 then
3
else
3)
else
(if i.val < 2583 then
3
else
(if i.val < 2584 then
3
else
3)))
else
(if i.val < 2587 then
(if i.val < 2586 then
3
else
3)
else
(if i.val < 2588 then
3
else
(if i.val < 2589 then
3
else
3))))
else
(if i.val < 2595 then
(if i.val < 2592 then
(if i.val < 2591 then
3
else
3)
else
(if i.val < 2593 then
3
else
(if i.val < 2594 then
3
else
3)))
else
(if i.val < 2597 then
(if i.val < 2596 then
3
else
3)
else
(if i.val < 2598 then
3
else
(if i.val < 2599 then
3
else
3))))))
else
(if i.val < 2620 then
(if i.val < 2610 then
(if i.val < 2605 then
(if i.val < 2602 then
(if i.val < 2601 then
3
else
3)
else
(if i.val < 2603 then
3
else
(if i.val < 2604 then
3
else
3)))
else
(if i.val < 2607 then
(if i.val < 2606 then
3
else
3)
else
(if i.val < 2608 then
3
else
(if i.val < 2609 then
3
else
3))))
else
(if i.val < 2615 then
(if i.val < 2612 then
(if i.val < 2611 then
3
else
3)
else
(if i.val < 2613 then
3
else
(if i.val < 2614 then
3
else
3)))
else
(if i.val < 2617 then
(if i.val < 2616 then
3
else
3)
else
(if i.val < 2618 then
3
else
(if i.val < 2619 then
3
else
3)))))
else
(if i.val < 2630 then
(if i.val < 2625 then
(if i.val < 2622 then
(if i.val < 2621 then
3
else
3)
else
(if i.val < 2623 then
3
else
(if i.val < 2624 then
3
else
3)))
else
(if i.val < 2627 then
(if i.val < 2626 then
3
else
3)
else
(if i.val < 2628 then
3
else
(if i.val < 2629 then
3
else
3))))
else
(if i.val < 2635 then
(if i.val < 2632 then
(if i.val < 2631 then
3
else
3)
else
(if i.val < 2633 then
3
else
(if i.val < 2634 then
3
else
3)))
else
(if i.val < 2637 then
(if i.val < 2636 then
3
else
3)
else
(if i.val < 2638 then
3
else
(if i.val < 2639 then
3
else
3)))))))
else
(if i.val < 2680 then
(if i.val < 2660 then
(if i.val < 2650 then
(if i.val < 2645 then
(if i.val < 2642 then
(if i.val < 2641 then
3
else
3)
else
(if i.val < 2643 then
3
else
(if i.val < 2644 then
3
else
3)))
else
(if i.val < 2647 then
(if i.val < 2646 then
3
else
3)
else
(if i.val < 2648 then
3
else
(if i.val < 2649 then
3
else
3))))
else
(if i.val < 2655 then
(if i.val < 2652 then
(if i.val < 2651 then
3
else
3)
else
(if i.val < 2653 then
3
else
(if i.val < 2654 then
3
else
3)))
else
(if i.val < 2657 then
(if i.val < 2656 then
3
else
3)
else
(if i.val < 2658 then
3
else
(if i.val < 2659 then
3
else
3)))))
else
(if i.val < 2670 then
(if i.val < 2665 then
(if i.val < 2662 then
(if i.val < 2661 then
3
else
3)
else
(if i.val < 2663 then
3
else
(if i.val < 2664 then
3
else
3)))
else
(if i.val < 2667 then
(if i.val < 2666 then
3
else
3)
else
(if i.val < 2668 then
3
else
(if i.val < 2669 then
3
else
3))))
else
(if i.val < 2675 then
(if i.val < 2672 then
(if i.val < 2671 then
3
else
3)
else
(if i.val < 2673 then
3
else
(if i.val < 2674 then
3
else
3)))
else
(if i.val < 2677 then
(if i.val < 2676 then
3
else
3)
else
(if i.val < 2678 then
3
else
(if i.val < 2679 then
3
else
3))))))
else
(if i.val < 2700 then
(if i.val < 2690 then
(if i.val < 2685 then
(if i.val < 2682 then
(if i.val < 2681 then
3
else
3)
else
(if i.val < 2683 then
3
else
(if i.val < 2684 then
3
else
3)))
else
(if i.val < 2687 then
(if i.val < 2686 then
3
else
3)
else
(if i.val < 2688 then
3
else
(if i.val < 2689 then
3
else
3))))
else
(if i.val < 2695 then
(if i.val < 2692 then
(if i.val < 2691 then
3
else
3)
else
(if i.val < 2693 then
3
else
(if i.val < 2694 then
3
else
3)))
else
(if i.val < 2697 then
(if i.val < 2696 then
3
else
3)
else
(if i.val < 2698 then
3
else
(if i.val < 2699 then
3
else
3)))))
else
(if i.val < 2710 then
(if i.val < 2705 then
(if i.val < 2702 then
(if i.val < 2701 then
3
else
3)
else
(if i.val < 2703 then
3
else
(if i.val < 2704 then
3
else
3)))
else
(if i.val < 2707 then
(if i.val < 2706 then
3
else
3)
else
(if i.val < 2708 then
3
else
(if i.val < 2709 then
3
else
3))))
else
(if i.val < 2715 then
(if i.val < 2712 then
(if i.val < 2711 then
3
else
3)
else
(if i.val < 2713 then
3
else
(if i.val < 2714 then
3
else
3)))
else
(if i.val < 2717 then
(if i.val < 2716 then
3
else
3)
else
(if i.val < 2718 then
3
else
(if i.val < 2719 then
3
else
3))))))))
else
(if i.val < 2800 then
(if i.val < 2760 then
(if i.val < 2740 then
(if i.val < 2730 then
(if i.val < 2725 then
(if i.val < 2722 then
(if i.val < 2721 then
3
else
3)
else
(if i.val < 2723 then
3
else
(if i.val < 2724 then
3
else
3)))
else
(if i.val < 2727 then
(if i.val < 2726 then
3
else
3)
else
(if i.val < 2728 then
3
else
(if i.val < 2729 then
3
else
3))))
else
(if i.val < 2735 then
(if i.val < 2732 then
(if i.val < 2731 then
3
else
3)
else
(if i.val < 2733 then
3
else
(if i.val < 2734 then
3
else
3)))
else
(if i.val < 2737 then
(if i.val < 2736 then
3
else
3)
else
(if i.val < 2738 then
3
else
(if i.val < 2739 then
3
else
3)))))
else
(if i.val < 2750 then
(if i.val < 2745 then
(if i.val < 2742 then
(if i.val < 2741 then
3
else
3)
else
(if i.val < 2743 then
3
else
(if i.val < 2744 then
3
else
3)))
else
(if i.val < 2747 then
(if i.val < 2746 then
3
else
3)
else
(if i.val < 2748 then
3
else
(if i.val < 2749 then
3
else
3))))
else
(if i.val < 2755 then
(if i.val < 2752 then
(if i.val < 2751 then
3
else
3)
else
(if i.val < 2753 then
3
else
(if i.val < 2754 then
3
else
3)))
else
(if i.val < 2757 then
(if i.val < 2756 then
3
else
3)
else
(if i.val < 2758 then
3
else
(if i.val < 2759 then
3
else
3))))))
else
(if i.val < 2780 then
(if i.val < 2770 then
(if i.val < 2765 then
(if i.val < 2762 then
(if i.val < 2761 then
3
else
3)
else
(if i.val < 2763 then
3
else
(if i.val < 2764 then
3
else
3)))
else
(if i.val < 2767 then
(if i.val < 2766 then
3
else
3)
else
(if i.val < 2768 then
3
else
(if i.val < 2769 then
3
else
3))))
else
(if i.val < 2775 then
(if i.val < 2772 then
(if i.val < 2771 then
3
else
3)
else
(if i.val < 2773 then
3
else
(if i.val < 2774 then
3
else
3)))
else
(if i.val < 2777 then
(if i.val < 2776 then
3
else
3)
else
(if i.val < 2778 then
3
else
(if i.val < 2779 then
3
else
3)))))
else
(if i.val < 2790 then
(if i.val < 2785 then
(if i.val < 2782 then
(if i.val < 2781 then
3
else
3)
else
(if i.val < 2783 then
3
else
(if i.val < 2784 then
3
else
3)))
else
(if i.val < 2787 then
(if i.val < 2786 then
3
else
3)
else
(if i.val < 2788 then
3
else
(if i.val < 2789 then
3
else
3))))
else
(if i.val < 2795 then
(if i.val < 2792 then
(if i.val < 2791 then
3
else
3)
else
(if i.val < 2793 then
3
else
(if i.val < 2794 then
3
else
3)))
else
(if i.val < 2797 then
(if i.val < 2796 then
3
else
3)
else
(if i.val < 2798 then
3
else
(if i.val < 2799 then
3
else
3)))))))
else
(if i.val < 2840 then
(if i.val < 2820 then
(if i.val < 2810 then
(if i.val < 2805 then
(if i.val < 2802 then
(if i.val < 2801 then
3
else
3)
else
(if i.val < 2803 then
3
else
(if i.val < 2804 then
3
else
3)))
else
(if i.val < 2807 then
(if i.val < 2806 then
3
else
3)
else
(if i.val < 2808 then
3
else
(if i.val < 2809 then
3
else
3))))
else
(if i.val < 2815 then
(if i.val < 2812 then
(if i.val < 2811 then
3
else
3)
else
(if i.val < 2813 then
3
else
(if i.val < 2814 then
3
else
3)))
else
(if i.val < 2817 then
(if i.val < 2816 then
3
else
3)
else
(if i.val < 2818 then
3
else
(if i.val < 2819 then
3
else
3)))))
else
(if i.val < 2830 then
(if i.val < 2825 then
(if i.val < 2822 then
(if i.val < 2821 then
3
else
3)
else
(if i.val < 2823 then
3
else
(if i.val < 2824 then
3
else
3)))
else
(if i.val < 2827 then
(if i.val < 2826 then
3
else
3)
else
(if i.val < 2828 then
3
else
(if i.val < 2829 then
3
else
3))))
else
(if i.val < 2835 then
(if i.val < 2832 then
(if i.val < 2831 then
3
else
3)
else
(if i.val < 2833 then
3
else
(if i.val < 2834 then
3
else
3)))
else
(if i.val < 2837 then
(if i.val < 2836 then
3
else
3)
else
(if i.val < 2838 then
3
else
(if i.val < 2839 then
3
else
3))))))
else
(if i.val < 2860 then
(if i.val < 2850 then
(if i.val < 2845 then
(if i.val < 2842 then
(if i.val < 2841 then
3
else
3)
else
(if i.val < 2843 then
3
else
(if i.val < 2844 then
3
else
3)))
else
(if i.val < 2847 then
(if i.val < 2846 then
3
else
3)
else
(if i.val < 2848 then
3
else
(if i.val < 2849 then
3
else
3))))
else
(if i.val < 2855 then
(if i.val < 2852 then
(if i.val < 2851 then
3
else
3)
else
(if i.val < 2853 then
3
else
(if i.val < 2854 then
3
else
3)))
else
(if i.val < 2857 then
(if i.val < 2856 then
3
else
3)
else
(if i.val < 2858 then
3
else
(if i.val < 2859 then
3
else
3)))))
else
(if i.val < 2870 then
(if i.val < 2865 then
(if i.val < 2862 then
(if i.val < 2861 then
3
else
3)
else
(if i.val < 2863 then
3
else
(if i.val < 2864 then
3
else
3)))
else
(if i.val < 2867 then
(if i.val < 2866 then
3
else
3)
else
(if i.val < 2868 then
3
else
(if i.val < 2869 then
3
else
3))))
else
(if i.val < 2875 then
(if i.val < 2872 then
(if i.val < 2871 then
3
else
3)
else
(if i.val < 2873 then
3
else
(if i.val < 2874 then
3
else
3)))
else
(if i.val < 2877 then
(if i.val < 2876 then
3
else
3)
else
(if i.val < 2878 then
3
else
(if i.val < 2879 then
3
else
3)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths2Part0000 : Fin 4368 → ℕ :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
2
else
2)
else
(if i.val < 3 then
2
else
2))
else
(if i.val < 6 then
(if i.val < 5 then
2
else
2)
else
(if i.val < 7 then
2
else
2)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
2
else
2)
else
(if i.val < 11 then
2
else
2))
else
(if i.val < 14 then
(if i.val < 13 then
2
else
2)
else
(if i.val < 15 then
2
else
2))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
2
else
2)
else
(if i.val < 19 then
2
else
2))
else
(if i.val < 22 then
(if i.val < 21 then
2
else
2)
else
(if i.val < 23 then
2
else
2)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
2
else
2)
else
(if i.val < 27 then
2
else
2))
else
(if i.val < 30 then
(if i.val < 29 then
2
else
2)
else
(if i.val < 31 then
2
else
2)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
2
else
2)
else
(if i.val < 35 then
2
else
2))
else
(if i.val < 38 then
(if i.val < 37 then
2
else
2)
else
(if i.val < 39 then
2
else
2)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
2
else
2)
else
(if i.val < 43 then
2
else
2))
else
(if i.val < 46 then
(if i.val < 45 then
2
else
2)
else
(if i.val < 47 then
2
else
2))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
2
else
2)
else
(if i.val < 51 then
2
else
2))
else
(if i.val < 54 then
(if i.val < 53 then
2
else
2)
else
(if i.val < 55 then
2
else
2)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
2
else
2)
else
(if i.val < 59 then
2
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
2
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
2
else
2))
else
(if i.val < 78 then
(if i.val < 77 then
2
else
2)
else
(if i.val < 79 then
2
else
2))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
2
else
2)
else
(if i.val < 83 then
2
else
2))
else
(if i.val < 86 then
(if i.val < 85 then
2
else
2)
else
(if i.val < 87 then
2
else
2)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
2
else
2)
else
(if i.val < 91 then
2
else
2))
else
(if i.val < 94 then
(if i.val < 93 then
2
else
2)
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
2
else
2)
else
(if i.val < 99 then
2
else
2))
else
(if i.val < 102 then
(if i.val < 101 then
2
else
2)
else
(if i.val < 103 then
2
else
2)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
2
else
2)
else
(if i.val < 107 then
2
else
2))
else
(if i.val < 110 then
(if i.val < 109 then
2
else
2)
else
(if i.val < 111 then
2
else
2))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
2
else
2)
else
(if i.val < 115 then
2
else
2))
else
(if i.val < 118 then
(if i.val < 117 then
2
else
2)
else
(if i.val < 119 then
2
else
2)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
2
else
2)
else
(if i.val < 123 then
2
else
2))
else
(if i.val < 126 then
(if i.val < 125 then
2
else
2)
else
(if i.val < 127 then
2
else
2)))))))
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
2
else
2))
else
(if i.val < 134 then
(if i.val < 133 then
2
else
2)
else
(if i.val < 135 then
2
else
2)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
2
else
2)
else
(if i.val < 139 then
2
else
2))
else
(if i.val < 142 then
(if i.val < 141 then
2
else
2)
else
(if i.val < 143 then
2
else
2))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
2
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
2
else
2)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
2
else
2)
else
(if i.val < 155 then
2
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
1))
else
(if i.val < 166 then
(if i.val < 165 then
2
else
2)
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
2
else
1)
else
(if i.val < 175 then
2
else
2))))
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
2
else
2)
else
(if i.val < 191 then
2
else
2))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
2
else
2)
else
(if i.val < 195 then
2
else
2))
else
(if i.val < 198 then
(if i.val < 197 then
2
else
2)
else
(if i.val < 199 then
2
else
2)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
2
else
2)
else
(if i.val < 203 then
2
else
2))
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
2
else
2)
else
(if i.val < 211 then
2
else
2))
else
(if i.val < 214 then
(if i.val < 213 then
2
else
2)
else
(if i.val < 215 then
2
else
2)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
2
else
2)
else
(if i.val < 219 then
2
else
2))
else
(if i.val < 222 then
(if i.val < 221 then
2
else
2)
else
(if i.val < 223 then
2
else
2)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
2
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
2
else
2)
else
(if i.val < 231 then
2
else
2)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
2
else
2)
else
(if i.val < 235 then
2
else
2))
else
(if i.val < 238 then
(if i.val < 237 then
2
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
2)
else
(if i.val < 243 then
2
else
2))
else
(if i.val < 246 then
(if i.val < 245 then
2
else
2)
else
(if i.val < 247 then
2
else
2)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
2
else
2)
else
(if i.val < 251 then
2
else
2))
else
(if i.val < 254 then
(if i.val < 253 then
2
else
2)
else
(if i.val < 255 then
2
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
2)
else
(if i.val < 259 then
2
else
2))
else
(if i.val < 262 then
(if i.val < 261 then
2
else
2)
else
(if i.val < 263 then
2
else
2)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
2
else
2)
else
(if i.val < 267 then
2
else
2))
else
(if i.val < 270 then
(if i.val < 269 then
2
else
2)
else
(if i.val < 271 then
2
else
2))))
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
2
else
2))
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
2))
else
(if i.val < 286 then
(if i.val < 285 then
2
else
2)
else
(if i.val < 287 then
2
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
2
else
2))
else
(if i.val < 294 then
(if i.val < 293 then
2
else
2)
else
(if i.val < 295 then
2
else
2)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
2
else
2)
else
(if i.val < 299 then
2
else
2))
else
(if i.val < 302 then
(if i.val < 301 then
2
else
2)
else
(if i.val < 303 then
2
else
2))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
2
else
2)
else
(if i.val < 307 then
2
else
2))
else
(if i.val < 310 then
(if i.val < 309 then
2
else
2)
else
(if i.val < 311 then
2
else
2)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
2
else
2)
else
(if i.val < 315 then
2
else
2))
else
(if i.val < 318 then
(if i.val < 317 then
2
else
2)
else
(if i.val < 319 then
2
else
2))))))
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
2)
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
2
else
2))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
2
else
2)
else
(if i.val < 339 then
2
else
2))
else
(if i.val < 342 then
(if i.val < 341 then
2
else
2)
else
(if i.val < 343 then
2
else
2)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
2
else
2)
else
(if i.val < 347 then
2
else
2))
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
2
else
2)
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
1)
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
2))
else
(if i.val < 382 then
(if i.val < 381 then
2
else
2)
else
(if i.val < 383 then
2
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
2
else
2)
else
(if i.val < 387 then
2
else
2))
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
2)
else
(if i.val < 415 then
2
else
2)))))
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
2
else
2))
else
(if i.val < 422 then
(if i.val < 421 then
2
else
2)
else
(if i.val < 423 then
2
else
2)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
2
else
2)
else
(if i.val < 427 then
2
else
2))
else
(if i.val < 430 then
(if i.val < 429 then
2
else
2)
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
2
else
2)
else
(if i.val < 435 then
2
else
2))
else
(if i.val < 438 then
(if i.val < 437 then
2
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
2))
else
(if i.val < 446 then
(if i.val < 445 then
2
else
2)
else
(if i.val < 447 then
2
else
2))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
2
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
2)
else
(if i.val < 455 then
2
else
2)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
2
else
2)
else
(if i.val < 459 then
2
else
2))
else
(if i.val < 462 then
(if i.val < 461 then
2
else
2)
else
(if i.val < 463 then
2
else
2))))
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
2
else
2))
else
(if i.val < 470 then
(if i.val < 469 then
2
else
2)
else
(if i.val < 471 then
2
else
2)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
2
else
2)
else
(if i.val < 475 then
2
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
2
else
2)))))
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
2)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
2
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
2))
else
(if i.val < 502 then
(if i.val < 501 then
2
else
2)
else
(if i.val < 503 then
2
else
2)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
2
else
2)
else
(if i.val < 507 then
2
else
2))
else
(if i.val < 510 then
(if i.val < 509 then
2
else
2)
else
(if i.val < 511 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths2Part0001 : Fin 4368 → ℕ :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
2
else
2)
else
(if i.val < 515 then
2
else
2))
else
(if i.val < 518 then
(if i.val < 517 then
2
else
2)
else
(if i.val < 519 then
2
else
2)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
2
else
2)
else
(if i.val < 523 then
2
else
2))
else
(if i.val < 526 then
(if i.val < 525 then
2
else
2)
else
(if i.val < 527 then
2
else
2))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
2
else
2)
else
(if i.val < 531 then
2
else
2))
else
(if i.val < 534 then
(if i.val < 533 then
2
else
2)
else
(if i.val < 535 then
2
else
2)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
2
else
2)
else
(if i.val < 539 then
2
else
2))
else
(if i.val < 542 then
(if i.val < 541 then
2
else
2)
else
(if i.val < 543 then
2
else
2)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
2
else
2)
else
(if i.val < 547 then
2
else
2))
else
(if i.val < 550 then
(if i.val < 549 then
2
else
2)
else
(if i.val < 551 then
2
else
2)))
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
2
else
2)
else
(if i.val < 559 then
2
else
2))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
2
else
2)
else
(if i.val < 563 then
2
else
2))
else
(if i.val < 566 then
(if i.val < 565 then
2
else
2)
else
(if i.val < 567 then
2
else
2)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
2
else
2)
else
(if i.val < 571 then
2
else
2))
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
2))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
2
else
2)
else
(if i.val < 579 then
2
else
2))
else
(if i.val < 582 then
(if i.val < 581 then
2
else
2)
else
(if i.val < 583 then
2
else
2)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
2
else
2)
else
(if i.val < 587 then
2
else
2))
else
(if i.val < 590 then
(if i.val < 589 then
2
else
2)
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
2
else
2)
else
(if i.val < 595 then
2
else
2))
else
(if i.val < 598 then
(if i.val < 597 then
2
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
2
else
2)
else
(if i.val < 603 then
2
else
2))
else
(if i.val < 606 then
(if i.val < 605 then
2
else
2)
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
2
else
2)
else
(if i.val < 611 then
2
else
2))
else
(if i.val < 614 then
(if i.val < 613 then
2
else
2)
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
2)
else
(if i.val < 619 then
2
else
2))
else
(if i.val < 622 then
(if i.val < 621 then
2
else
2)
else
(if i.val < 623 then
2
else
2))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
2
else
2)
else
(if i.val < 627 then
2
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
2
else
2))
else
(if i.val < 646 then
(if i.val < 645 then
2
else
2)
else
(if i.val < 647 then
2
else
2)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
2
else
2)
else
(if i.val < 651 then
2
else
2))
else
(if i.val < 654 then
(if i.val < 653 then
2
else
2)
else
(if i.val < 655 then
2
else
2))))
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
2
else
2))
else
(if i.val < 662 then
(if i.val < 661 then
2
else
2)
else
(if i.val < 663 then
2
else
2)))
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
2)
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
2
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
2
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
2)
else
(if i.val < 691 then
2
else
2))
else
(if i.val < 694 then
(if i.val < 693 then
2
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
2
else
2)
else
(if i.val < 699 then
2
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
2
else
2)
else
(if i.val < 711 then
2
else
2)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
2
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
2))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
2
else
2)
else
(if i.val < 723 then
2
else
2))
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
2)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
2
else
2)
else
(if i.val < 739 then
2
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
2)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
2
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
2)
else
(if i.val < 751 then
2
else
2))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
2
else
2)
else
(if i.val < 755 then
2
else
2))
else
(if i.val < 758 then
(if i.val < 757 then
2
else
2)
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
2)
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
2)
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
2
else
2)
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
2
else
2))
else
(if i.val < 782 then
(if i.val < 781 then
2
else
2)
else
(if i.val < 783 then
2
else
2))))
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
2
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
2))
else
(if i.val < 798 then
(if i.val < 797 then
2
else
2)
else
(if i.val < 799 then
2
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
2)
else
(if i.val < 803 then
2
else
2))
else
(if i.val < 806 then
(if i.val < 805 then
2
else
2)
else
(if i.val < 807 then
2
else
2)))
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
2))
else
(if i.val < 814 then
(if i.val < 813 then
2
else
2)
else
(if i.val < 815 then
2
else
2))))
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
2
else
2))
else
(if i.val < 822 then
(if i.val < 821 then
2
else
2)
else
(if i.val < 823 then
2
else
2)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
2
else
2)
else
(if i.val < 827 then
2
else
2))
else
(if i.val < 830 then
(if i.val < 829 then
2
else
2)
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
2
else
2))
else
(if i.val < 838 then
(if i.val < 837 then
2
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
2
else
2)
else
(if i.val < 843 then
2
else
2))
else
(if i.val < 846 then
(if i.val < 845 then
2
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
2
else
2)
else
(if i.val < 851 then
2
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
2)))
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
2)
else
(if i.val < 863 then
2
else
2)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
2
else
2)
else
(if i.val < 867 then
2
else
2))
else
(if i.val < 870 then
(if i.val < 869 then
2
else
2)
else
(if i.val < 871 then
2
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
2
else
2)
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
2
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
2
else
2)
else
(if i.val < 895 then
2
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
2
else
2)
else
(if i.val < 899 then
2
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
2
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
2))
else
(if i.val < 910 then
(if i.val < 909 then
2
else
2)
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
2
else
2)
else
(if i.val < 915 then
2
else
2))
else
(if i.val < 918 then
(if i.val < 917 then
2
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
2))
else
(if i.val < 926 then
(if i.val < 925 then
2
else
2)
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
2
else
2)
else
(if i.val < 931 then
2
else
2))
else
(if i.val < 934 then
(if i.val < 933 then
2
else
2)
else
(if i.val < 935 then
2
else
2)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
2
else
2)
else
(if i.val < 939 then
2
else
2))
else
(if i.val < 942 then
(if i.val < 941 then
2
else
2)
else
(if i.val < 943 then
2
else
2))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
2
else
2)
else
(if i.val < 947 then
2
else
2))
else
(if i.val < 950 then
(if i.val < 949 then
2
else
2)
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
2
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
2
else
2))))))
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
2
else
2)
else
(if i.val < 975 then
2
else
2))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
2
else
2)
else
(if i.val < 979 then
2
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
2)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
2
else
2)
else
(if i.val < 995 then
2
else
2))
else
(if i.val < 998 then
(if i.val < 997 then
2
else
2)
else
(if i.val < 999 then
2
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
2
else
2))
else
(if i.val < 1006 then
(if i.val < 1005 then
2
else
2)
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
2
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
2))
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

def g32p_row31_cosetLengths2Part0002 : Fin 4368 → ℕ :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
2
else
2)
else
(if i.val < 1027 then
2
else
2))
else
(if i.val < 1030 then
(if i.val < 1029 then
2
else
2)
else
(if i.val < 1031 then
2
else
2)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
2
else
2)
else
(if i.val < 1035 then
2
else
2))
else
(if i.val < 1038 then
(if i.val < 1037 then
2
else
2)
else
(if i.val < 1039 then
2
else
2))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
2
else
2)
else
(if i.val < 1043 then
2
else
2))
else
(if i.val < 1046 then
(if i.val < 1045 then
2
else
2)
else
(if i.val < 1047 then
2
else
2)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
2
else
2)
else
(if i.val < 1051 then
2
else
2))
else
(if i.val < 1054 then
(if i.val < 1053 then
2
else
2)
else
(if i.val < 1055 then
2
else
2)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
2
else
2)
else
(if i.val < 1059 then
2
else
2))
else
(if i.val < 1062 then
(if i.val < 1061 then
2
else
2)
else
(if i.val < 1063 then
2
else
2)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
2
else
2)
else
(if i.val < 1067 then
2
else
1))
else
(if i.val < 1070 then
(if i.val < 1069 then
2
else
2)
else
(if i.val < 1071 then
2
else
2))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
2
else
2)
else
(if i.val < 1075 then
2
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
2
else
2)))
else
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
2))
else
(if i.val < 1086 then
(if i.val < 1085 then
2
else
2)
else
(if i.val < 1087 then
2
else
2))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
2
else
2)
else
(if i.val < 1091 then
2
else
2))
else
(if i.val < 1094 then
(if i.val < 1093 then
2
else
2)
else
(if i.val < 1095 then
2
else
2)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
2
else
2)
else
(if i.val < 1099 then
2
else
2))
else
(if i.val < 1102 then
(if i.val < 1101 then
2
else
2)
else
(if i.val < 1103 then
2
else
2))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
2
else
2)
else
(if i.val < 1107 then
2
else
2))
else
(if i.val < 1110 then
(if i.val < 1109 then
2
else
2)
else
(if i.val < 1111 then
2
else
2)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
2
else
2)
else
(if i.val < 1115 then
2
else
2))
else
(if i.val < 1118 then
(if i.val < 1117 then
2
else
2)
else
(if i.val < 1119 then
2
else
2)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
2
else
2)
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
2)
else
(if i.val < 1127 then
2
else
2)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
2
else
2)
else
(if i.val < 1131 then
2
else
2))
else
(if i.val < 1134 then
(if i.val < 1133 then
2
else
2)
else
(if i.val < 1135 then
2
else
2))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
2
else
2)
else
(if i.val < 1139 then
2
else
2))
else
(if i.val < 1142 then
(if i.val < 1141 then
2
else
2)
else
(if i.val < 1143 then
2
else
2)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
2
else
2)
else
(if i.val < 1147 then
2
else
2))
else
(if i.val < 1150 then
(if i.val < 1149 then
2
else
2)
else
(if i.val < 1151 then
1
else
2)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
2
else
2)
else
(if i.val < 1155 then
2
else
2))
else
(if i.val < 1158 then
(if i.val < 1157 then
2
else
2)
else
(if i.val < 1159 then
2
else
2)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
2
else
2)
else
(if i.val < 1163 then
2
else
2))
else
(if i.val < 1166 then
(if i.val < 1165 then
2
else
2)
else
(if i.val < 1167 then
2
else
2))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
2
else
2)
else
(if i.val < 1171 then
2
else
2))
else
(if i.val < 1174 then
(if i.val < 1173 then
2
else
2)
else
(if i.val < 1175 then
2
else
2)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
2
else
2)
else
(if i.val < 1179 then
2
else
1))
else
(if i.val < 1182 then
(if i.val < 1181 then
2
else
2)
else
(if i.val < 1183 then
2
else
2)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
2
else
2)
else
(if i.val < 1187 then
2
else
2))
else
(if i.val < 1190 then
(if i.val < 1189 then
2
else
2)
else
(if i.val < 1191 then
2
else
2)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
2
else
2)
else
(if i.val < 1195 then
2
else
2))
else
(if i.val < 1198 then
(if i.val < 1197 then
2
else
2)
else
(if i.val < 1199 then
2
else
2))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
2
else
2)
else
(if i.val < 1203 then
2
else
2))
else
(if i.val < 1206 then
(if i.val < 1205 then
2
else
2)
else
(if i.val < 1207 then
2
else
2)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
2
else
2)
else
(if i.val < 1211 then
2
else
2))
else
(if i.val < 1214 then
(if i.val < 1213 then
2
else
2)
else
(if i.val < 1215 then
2
else
2))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
2
else
2)
else
(if i.val < 1219 then
2
else
2))
else
(if i.val < 1222 then
(if i.val < 1221 then
2
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
2
else
2)
else
(if i.val < 1227 then
2
else
2))
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
2))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
2
else
2)
else
(if i.val < 1235 then
2
else
2))
else
(if i.val < 1238 then
(if i.val < 1237 then
2
else
2)
else
(if i.val < 1239 then
2
else
2)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
2
else
2)
else
(if i.val < 1243 then
2
else
2))
else
(if i.val < 1246 then
(if i.val < 1245 then
2
else
2)
else
(if i.val < 1247 then
2
else
2)))))
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
2
else
2)
else
(if i.val < 1255 then
2
else
2)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
2
else
2)
else
(if i.val < 1259 then
2
else
2))
else
(if i.val < 1262 then
(if i.val < 1261 then
2
else
2)
else
(if i.val < 1263 then
2
else
2))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
2
else
2)
else
(if i.val < 1267 then
2
else
2))
else
(if i.val < 1270 then
(if i.val < 1269 then
2
else
2)
else
(if i.val < 1271 then
2
else
2)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
2
else
2)
else
(if i.val < 1275 then
2
else
2))
else
(if i.val < 1278 then
(if i.val < 1277 then
2
else
2)
else
(if i.val < 1279 then
2
else
2))))))))
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
2)
else
(if i.val < 1283 then
2
else
2))
else
(if i.val < 1286 then
(if i.val < 1285 then
2
else
2)
else
(if i.val < 1287 then
2
else
2)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
2
else
2)
else
(if i.val < 1291 then
2
else
2))
else
(if i.val < 1294 then
(if i.val < 1293 then
2
else
2)
else
(if i.val < 1295 then
2
else
2))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
2
else
2)
else
(if i.val < 1299 then
2
else
2))
else
(if i.val < 1302 then
(if i.val < 1301 then
2
else
2)
else
(if i.val < 1303 then
2
else
2)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
2
else
2)
else
(if i.val < 1307 then
2
else
2))
else
(if i.val < 1310 then
(if i.val < 1309 then
2
else
2)
else
(if i.val < 1311 then
2
else
2)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
2
else
2)
else
(if i.val < 1315 then
2
else
2))
else
(if i.val < 1318 then
(if i.val < 1317 then
2
else
2)
else
(if i.val < 1319 then
2
else
2)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
2
else
2)
else
(if i.val < 1323 then
2
else
2))
else
(if i.val < 1326 then
(if i.val < 1325 then
2
else
2)
else
(if i.val < 1327 then
2
else
2))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
2
else
2)
else
(if i.val < 1331 then
2
else
2))
else
(if i.val < 1334 then
(if i.val < 1333 then
2
else
2)
else
(if i.val < 1335 then
2
else
2)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
2
else
2)
else
(if i.val < 1339 then
2
else
2))
else
(if i.val < 1342 then
(if i.val < 1341 then
2
else
2)
else
(if i.val < 1343 then
2
else
2))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
2
else
2)
else
(if i.val < 1347 then
2
else
2))
else
(if i.val < 1350 then
(if i.val < 1349 then
2
else
2)
else
(if i.val < 1351 then
2
else
2)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
2
else
2)
else
(if i.val < 1355 then
2
else
2))
else
(if i.val < 1358 then
(if i.val < 1357 then
2
else
2)
else
(if i.val < 1359 then
2
else
2))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
2
else
2)
else
(if i.val < 1363 then
2
else
2))
else
(if i.val < 1366 then
(if i.val < 1365 then
2
else
2)
else
(if i.val < 1367 then
2
else
2)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
2
else
2)
else
(if i.val < 1371 then
2
else
2))
else
(if i.val < 1374 then
(if i.val < 1373 then
2
else
2)
else
(if i.val < 1375 then
2
else
2)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
2
else
1)
else
(if i.val < 1379 then
2
else
2))
else
(if i.val < 1382 then
(if i.val < 1381 then
2
else
2)
else
(if i.val < 1383 then
2
else
2)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
2
else
2)
else
(if i.val < 1387 then
2
else
2))
else
(if i.val < 1390 then
(if i.val < 1389 then
2
else
2)
else
(if i.val < 1391 then
2
else
2))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
2
else
2)
else
(if i.val < 1395 then
2
else
2))
else
(if i.val < 1398 then
(if i.val < 1397 then
2
else
2)
else
(if i.val < 1399 then
2
else
2)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
2
else
2)
else
(if i.val < 1403 then
2
else
2))
else
(if i.val < 1406 then
(if i.val < 1405 then
2
else
2)
else
(if i.val < 1407 then
2
else
2)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
2
else
2)
else
(if i.val < 1411 then
2
else
2))
else
(if i.val < 1414 then
(if i.val < 1413 then
2
else
2)
else
(if i.val < 1415 then
2
else
2)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
2
else
2)
else
(if i.val < 1419 then
2
else
2))
else
(if i.val < 1422 then
(if i.val < 1421 then
2
else
2)
else
(if i.val < 1423 then
2
else
2))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
2
else
2)
else
(if i.val < 1427 then
2
else
2))
else
(if i.val < 1430 then
(if i.val < 1429 then
2
else
2)
else
(if i.val < 1431 then
2
else
2)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
2
else
2)
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
2)
else
(if i.val < 1439 then
2
else
2)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
2
else
2)
else
(if i.val < 1443 then
2
else
2))
else
(if i.val < 1446 then
(if i.val < 1445 then
2
else
2)
else
(if i.val < 1447 then
2
else
2)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
2
else
2)
else
(if i.val < 1451 then
2
else
2))
else
(if i.val < 1454 then
(if i.val < 1453 then
2
else
2)
else
(if i.val < 1455 then
2
else
2))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
2
else
2)
else
(if i.val < 1459 then
2
else
2))
else
(if i.val < 1462 then
(if i.val < 1461 then
2
else
2)
else
(if i.val < 1463 then
2
else
2)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
2
else
2)
else
(if i.val < 1467 then
2
else
2))
else
(if i.val < 1470 then
(if i.val < 1469 then
2
else
2)
else
(if i.val < 1471 then
2
else
2))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
2
else
2)
else
(if i.val < 1475 then
2
else
2))
else
(if i.val < 1478 then
(if i.val < 1477 then
2
else
2)
else
(if i.val < 1479 then
2
else
2)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
2
else
2)
else
(if i.val < 1483 then
2
else
2))
else
(if i.val < 1486 then
(if i.val < 1485 then
2
else
2)
else
(if i.val < 1487 then
2
else
2))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
2
else
2)
else
(if i.val < 1491 then
2
else
2))
else
(if i.val < 1494 then
(if i.val < 1493 then
2
else
2)
else
(if i.val < 1495 then
2
else
2)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
2
else
2)
else
(if i.val < 1499 then
2
else
2))
else
(if i.val < 1502 then
(if i.val < 1501 then
2
else
2)
else
(if i.val < 1503 then
2
else
2)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
2
else
2)
else
(if i.val < 1507 then
2
else
2))
else
(if i.val < 1510 then
(if i.val < 1509 then
2
else
2)
else
(if i.val < 1511 then
2
else
2)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
2
else
2)
else
(if i.val < 1515 then
2
else
2))
else
(if i.val < 1518 then
(if i.val < 1517 then
2
else
2)
else
(if i.val < 1519 then
2
else
2))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
2
else
2)
else
(if i.val < 1523 then
2
else
2))
else
(if i.val < 1526 then
(if i.val < 1525 then
2
else
2)
else
(if i.val < 1527 then
2
else
2)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
2
else
2)
else
(if i.val < 1531 then
2
else
2))
else
(if i.val < 1534 then
(if i.val < 1533 then
2
else
2)
else
(if i.val < 1535 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths2Part0003 : Fin 4368 → ℕ :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
2
else
2)
else
(if i.val < 1539 then
2
else
2))
else
(if i.val < 1542 then
(if i.val < 1541 then
2
else
2)
else
(if i.val < 1543 then
2
else
1)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
2
else
2)
else
(if i.val < 1547 then
2
else
2))
else
(if i.val < 1550 then
(if i.val < 1549 then
2
else
2)
else
(if i.val < 1551 then
2
else
2))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
2
else
2)
else
(if i.val < 1555 then
2
else
2))
else
(if i.val < 1558 then
(if i.val < 1557 then
2
else
2)
else
(if i.val < 1559 then
2
else
2)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
2
else
2)
else
(if i.val < 1563 then
2
else
2))
else
(if i.val < 1566 then
(if i.val < 1565 then
2
else
2)
else
(if i.val < 1567 then
2
else
2)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
2
else
2)
else
(if i.val < 1571 then
2
else
2))
else
(if i.val < 1574 then
(if i.val < 1573 then
2
else
2)
else
(if i.val < 1575 then
2
else
2)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
2
else
2)
else
(if i.val < 1579 then
2
else
2))
else
(if i.val < 1582 then
(if i.val < 1581 then
2
else
2)
else
(if i.val < 1583 then
2
else
2))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
2
else
2)
else
(if i.val < 1587 then
2
else
2))
else
(if i.val < 1590 then
(if i.val < 1589 then
2
else
2)
else
(if i.val < 1591 then
2
else
2)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
2
else
2)
else
(if i.val < 1595 then
2
else
2))
else
(if i.val < 1598 then
(if i.val < 1597 then
2
else
2)
else
(if i.val < 1599 then
2
else
2))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
2
else
2)
else
(if i.val < 1603 then
2
else
2))
else
(if i.val < 1606 then
(if i.val < 1605 then
2
else
2)
else
(if i.val < 1607 then
2
else
2)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
2
else
2)
else
(if i.val < 1611 then
2
else
2))
else
(if i.val < 1614 then
(if i.val < 1613 then
2
else
2)
else
(if i.val < 1615 then
2
else
2))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
2
else
2)
else
(if i.val < 1619 then
2
else
2))
else
(if i.val < 1622 then
(if i.val < 1621 then
2
else
2)
else
(if i.val < 1623 then
2
else
2)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
2
else
2)
else
(if i.val < 1627 then
2
else
2))
else
(if i.val < 1630 then
(if i.val < 1629 then
2
else
2)
else
(if i.val < 1631 then
2
else
2)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
2
else
2)
else
(if i.val < 1635 then
2
else
2))
else
(if i.val < 1638 then
(if i.val < 1637 then
2
else
2)
else
(if i.val < 1639 then
2
else
2)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
2
else
2)
else
(if i.val < 1643 then
2
else
2))
else
(if i.val < 1646 then
(if i.val < 1645 then
2
else
2)
else
(if i.val < 1647 then
2
else
2))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
2
else
2)
else
(if i.val < 1651 then
2
else
2))
else
(if i.val < 1654 then
(if i.val < 1653 then
2
else
2)
else
(if i.val < 1655 then
2
else
2)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
2
else
2)
else
(if i.val < 1659 then
2
else
2))
else
(if i.val < 1662 then
(if i.val < 1661 then
2
else
2)
else
(if i.val < 1663 then
2
else
2)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
2
else
2)
else
(if i.val < 1667 then
2
else
2))
else
(if i.val < 1670 then
(if i.val < 1669 then
2
else
2)
else
(if i.val < 1671 then
2
else
2)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
2
else
2)
else
(if i.val < 1675 then
2
else
2))
else
(if i.val < 1678 then
(if i.val < 1677 then
2
else
2)
else
(if i.val < 1679 then
2
else
2))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
2
else
2)
else
(if i.val < 1683 then
2
else
2))
else
(if i.val < 1686 then
(if i.val < 1685 then
2
else
2)
else
(if i.val < 1687 then
2
else
2)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
2
else
2)
else
(if i.val < 1691 then
2
else
2))
else
(if i.val < 1694 then
(if i.val < 1693 then
2
else
2)
else
(if i.val < 1695 then
2
else
2)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
2
else
2)
else
(if i.val < 1699 then
2
else
2))
else
(if i.val < 1702 then
(if i.val < 1701 then
2
else
2)
else
(if i.val < 1703 then
2
else
2)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
2
else
2)
else
(if i.val < 1707 then
2
else
2))
else
(if i.val < 1710 then
(if i.val < 1709 then
2
else
2)
else
(if i.val < 1711 then
2
else
2))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
2
else
2)
else
(if i.val < 1715 then
2
else
2))
else
(if i.val < 1718 then
(if i.val < 1717 then
2
else
2)
else
(if i.val < 1719 then
2
else
2)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
2
else
2)
else
(if i.val < 1723 then
2
else
2))
else
(if i.val < 1726 then
(if i.val < 1725 then
2
else
2)
else
(if i.val < 1727 then
2
else
2))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
2
else
2)
else
(if i.val < 1731 then
2
else
2))
else
(if i.val < 1734 then
(if i.val < 1733 then
2
else
2)
else
(if i.val < 1735 then
2
else
2)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
2
else
2)
else
(if i.val < 1739 then
2
else
2))
else
(if i.val < 1742 then
(if i.val < 1741 then
2
else
2)
else
(if i.val < 1743 then
2
else
2))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
2
else
2)
else
(if i.val < 1747 then
2
else
2))
else
(if i.val < 1750 then
(if i.val < 1749 then
2
else
2)
else
(if i.val < 1751 then
2
else
2)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
2
else
2)
else
(if i.val < 1755 then
2
else
2))
else
(if i.val < 1758 then
(if i.val < 1757 then
2
else
2)
else
(if i.val < 1759 then
2
else
2)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
2
else
2)
else
(if i.val < 1763 then
2
else
2))
else
(if i.val < 1766 then
(if i.val < 1765 then
2
else
2)
else
(if i.val < 1767 then
2
else
2)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
2
else
2)
else
(if i.val < 1771 then
2
else
2))
else
(if i.val < 1774 then
(if i.val < 1773 then
2
else
2)
else
(if i.val < 1775 then
2
else
2))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
2
else
2)
else
(if i.val < 1779 then
2
else
2))
else
(if i.val < 1782 then
(if i.val < 1781 then
2
else
2)
else
(if i.val < 1783 then
2
else
2)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
2
else
2)
else
(if i.val < 1787 then
2
else
2))
else
(if i.val < 1790 then
(if i.val < 1789 then
2
else
2)
else
(if i.val < 1791 then
2
else
2))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
2
else
2)
else
(if i.val < 1795 then
2
else
2))
else
(if i.val < 1798 then
(if i.val < 1797 then
2
else
2)
else
(if i.val < 1799 then
2
else
2)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
2
else
2)
else
(if i.val < 1803 then
2
else
2))
else
(if i.val < 1806 then
(if i.val < 1805 then
2
else
2)
else
(if i.val < 1807 then
2
else
2))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
2
else
2)
else
(if i.val < 1811 then
2
else
2))
else
(if i.val < 1814 then
(if i.val < 1813 then
2
else
2)
else
(if i.val < 1815 then
2
else
2)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
2
else
2)
else
(if i.val < 1819 then
2
else
2))
else
(if i.val < 1822 then
(if i.val < 1821 then
2
else
2)
else
(if i.val < 1823 then
2
else
2)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
2
else
2)
else
(if i.val < 1827 then
2
else
2))
else
(if i.val < 1830 then
(if i.val < 1829 then
2
else
2)
else
(if i.val < 1831 then
2
else
2)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
2
else
2)
else
(if i.val < 1835 then
2
else
2))
else
(if i.val < 1838 then
(if i.val < 1837 then
2
else
2)
else
(if i.val < 1839 then
2
else
2))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
2
else
2)
else
(if i.val < 1843 then
2
else
2))
else
(if i.val < 1846 then
(if i.val < 1845 then
2
else
2)
else
(if i.val < 1847 then
2
else
2)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
2
else
2)
else
(if i.val < 1851 then
2
else
2))
else
(if i.val < 1854 then
(if i.val < 1853 then
2
else
2)
else
(if i.val < 1855 then
2
else
2))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
2
else
2)
else
(if i.val < 1859 then
2
else
2))
else
(if i.val < 1862 then
(if i.val < 1861 then
2
else
2)
else
(if i.val < 1863 then
2
else
2)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
1
else
2)
else
(if i.val < 1867 then
2
else
2))
else
(if i.val < 1870 then
(if i.val < 1869 then
2
else
2)
else
(if i.val < 1871 then
2
else
2))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
2
else
2)
else
(if i.val < 1875 then
2
else
2))
else
(if i.val < 1878 then
(if i.val < 1877 then
2
else
2)
else
(if i.val < 1879 then
2
else
2)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
2
else
2)
else
(if i.val < 1883 then
2
else
2))
else
(if i.val < 1886 then
(if i.val < 1885 then
2
else
2)
else
(if i.val < 1887 then
2
else
2)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
2
else
2)
else
(if i.val < 1891 then
2
else
2))
else
(if i.val < 1894 then
(if i.val < 1893 then
2
else
2)
else
(if i.val < 1895 then
2
else
2)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
2
else
2)
else
(if i.val < 1899 then
2
else
2))
else
(if i.val < 1902 then
(if i.val < 1901 then
2
else
2)
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
2
else
2)
else
(if i.val < 1907 then
2
else
2))
else
(if i.val < 1910 then
(if i.val < 1909 then
2
else
2)
else
(if i.val < 1911 then
2
else
2)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
2
else
2)
else
(if i.val < 1915 then
2
else
2))
else
(if i.val < 1918 then
(if i.val < 1917 then
2
else
2)
else
(if i.val < 1919 then
2
else
2)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
2
else
2)
else
(if i.val < 1923 then
2
else
2))
else
(if i.val < 1926 then
(if i.val < 1925 then
2
else
2)
else
(if i.val < 1927 then
2
else
2)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
2
else
2)
else
(if i.val < 1931 then
2
else
2))
else
(if i.val < 1934 then
(if i.val < 1933 then
2
else
2)
else
(if i.val < 1935 then
2
else
2))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
2
else
2)
else
(if i.val < 1939 then
2
else
2))
else
(if i.val < 1942 then
(if i.val < 1941 then
2
else
2)
else
(if i.val < 1943 then
2
else
1)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
2
else
2)
else
(if i.val < 1947 then
2
else
2))
else
(if i.val < 1950 then
(if i.val < 1949 then
2
else
2)
else
(if i.val < 1951 then
2
else
2)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
2
else
2)
else
(if i.val < 1955 then
2
else
1))
else
(if i.val < 1958 then
(if i.val < 1957 then
2
else
2)
else
(if i.val < 1959 then
2
else
2)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
2
else
2)
else
(if i.val < 1963 then
2
else
2))
else
(if i.val < 1966 then
(if i.val < 1965 then
2
else
2)
else
(if i.val < 1967 then
2
else
2))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
2
else
2)
else
(if i.val < 1971 then
2
else
2))
else
(if i.val < 1974 then
(if i.val < 1973 then
2
else
1)
else
(if i.val < 1975 then
2
else
2)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
2
else
2)
else
(if i.val < 1979 then
2
else
2))
else
(if i.val < 1982 then
(if i.val < 1981 then
2
else
2)
else
(if i.val < 1983 then
2
else
2))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
2
else
2)
else
(if i.val < 1987 then
2
else
2))
else
(if i.val < 1990 then
(if i.val < 1989 then
2
else
2)
else
(if i.val < 1991 then
2
else
2)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
2
else
2)
else
(if i.val < 1995 then
2
else
2))
else
(if i.val < 1998 then
(if i.val < 1997 then
2
else
2)
else
(if i.val < 1999 then
2
else
2))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
2
else
2)
else
(if i.val < 2003 then
2
else
2))
else
(if i.val < 2006 then
(if i.val < 2005 then
2
else
2)
else
(if i.val < 2007 then
2
else
2)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
2
else
2)
else
(if i.val < 2011 then
2
else
2))
else
(if i.val < 2014 then
(if i.val < 2013 then
2
else
2)
else
(if i.val < 2015 then
2
else
2)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
2
else
2)
else
(if i.val < 2019 then
2
else
2))
else
(if i.val < 2022 then
(if i.val < 2021 then
2
else
2)
else
(if i.val < 2023 then
2
else
2)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
2
else
2)
else
(if i.val < 2027 then
2
else
2))
else
(if i.val < 2030 then
(if i.val < 2029 then
2
else
2)
else
(if i.val < 2031 then
2
else
2))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
2
else
2)
else
(if i.val < 2035 then
2
else
2))
else
(if i.val < 2038 then
(if i.val < 2037 then
2
else
2)
else
(if i.val < 2039 then
2
else
2)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
2
else
2)
else
(if i.val < 2043 then
2
else
2))
else
(if i.val < 2046 then
(if i.val < 2045 then
2
else
2)
else
(if i.val < 2047 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths2Part0004 : Fin 4368 → ℕ :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
2
else
2)
else
(if i.val < 2051 then
2
else
2))
else
(if i.val < 2054 then
(if i.val < 2053 then
2
else
2)
else
(if i.val < 2055 then
2
else
2)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
2
else
2)
else
(if i.val < 2059 then
2
else
2))
else
(if i.val < 2062 then
(if i.val < 2061 then
2
else
2)
else
(if i.val < 2063 then
2
else
2))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
2
else
2)
else
(if i.val < 2067 then
2
else
2))
else
(if i.val < 2070 then
(if i.val < 2069 then
2
else
2)
else
(if i.val < 2071 then
2
else
2)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
2
else
2)
else
(if i.val < 2075 then
2
else
2))
else
(if i.val < 2078 then
(if i.val < 2077 then
2
else
2)
else
(if i.val < 2079 then
2
else
2)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
2
else
2)
else
(if i.val < 2083 then
2
else
2))
else
(if i.val < 2086 then
(if i.val < 2085 then
2
else
2)
else
(if i.val < 2087 then
2
else
2)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
2
else
2)
else
(if i.val < 2091 then
2
else
2))
else
(if i.val < 2094 then
(if i.val < 2093 then
2
else
2)
else
(if i.val < 2095 then
2
else
2))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
2
else
2)
else
(if i.val < 2099 then
2
else
2))
else
(if i.val < 2102 then
(if i.val < 2101 then
2
else
2)
else
(if i.val < 2103 then
2
else
2)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
2
else
2)
else
(if i.val < 2107 then
2
else
2))
else
(if i.val < 2110 then
(if i.val < 2109 then
2
else
2)
else
(if i.val < 2111 then
2
else
2))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
2
else
2)
else
(if i.val < 2115 then
2
else
2))
else
(if i.val < 2118 then
(if i.val < 2117 then
2
else
2)
else
(if i.val < 2119 then
2
else
2)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
2
else
2)
else
(if i.val < 2123 then
2
else
2))
else
(if i.val < 2126 then
(if i.val < 2125 then
2
else
2)
else
(if i.val < 2127 then
2
else
2))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
2
else
2)
else
(if i.val < 2131 then
2
else
2))
else
(if i.val < 2134 then
(if i.val < 2133 then
2
else
2)
else
(if i.val < 2135 then
2
else
2)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
2
else
2)
else
(if i.val < 2139 then
2
else
2))
else
(if i.val < 2142 then
(if i.val < 2141 then
2
else
2)
else
(if i.val < 2143 then
2
else
2)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
2
else
2)
else
(if i.val < 2147 then
2
else
2))
else
(if i.val < 2150 then
(if i.val < 2149 then
2
else
2)
else
(if i.val < 2151 then
2
else
2)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
2
else
2)
else
(if i.val < 2155 then
2
else
2))
else
(if i.val < 2158 then
(if i.val < 2157 then
2
else
1)
else
(if i.val < 2159 then
2
else
2))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
1
else
2)
else
(if i.val < 2163 then
2
else
2))
else
(if i.val < 2166 then
(if i.val < 2165 then
2
else
2)
else
(if i.val < 2167 then
2
else
2)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
2
else
2)
else
(if i.val < 2171 then
2
else
2))
else
(if i.val < 2174 then
(if i.val < 2173 then
2
else
2)
else
(if i.val < 2175 then
2
else
1)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
2
else
2)
else
(if i.val < 2179 then
2
else
2))
else
(if i.val < 2182 then
(if i.val < 2181 then
2
else
2)
else
(if i.val < 2183 then
2
else
2)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
2
else
2)
else
(if i.val < 2187 then
2
else
2))
else
(if i.val < 2190 then
(if i.val < 2189 then
2
else
2)
else
(if i.val < 2191 then
2
else
2))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
2
else
2)
else
(if i.val < 2195 then
2
else
2))
else
(if i.val < 2198 then
(if i.val < 2197 then
2
else
2)
else
(if i.val < 2199 then
2
else
2)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
2
else
2)
else
(if i.val < 2203 then
1
else
2))
else
(if i.val < 2206 then
(if i.val < 2205 then
2
else
2)
else
(if i.val < 2207 then
2
else
2)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
2
else
2)
else
(if i.val < 2211 then
2
else
2))
else
(if i.val < 2214 then
(if i.val < 2213 then
2
else
2)
else
(if i.val < 2215 then
2
else
2)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
2
else
2)
else
(if i.val < 2219 then
2
else
2))
else
(if i.val < 2222 then
(if i.val < 2221 then
2
else
2)
else
(if i.val < 2223 then
2
else
2))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
2
else
2)
else
(if i.val < 2227 then
2
else
1))
else
(if i.val < 2230 then
(if i.val < 2229 then
2
else
2)
else
(if i.val < 2231 then
2
else
2)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
2
else
2)
else
(if i.val < 2235 then
2
else
2))
else
(if i.val < 2238 then
(if i.val < 2237 then
2
else
2)
else
(if i.val < 2239 then
2
else
2))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
2
else
2)
else
(if i.val < 2243 then
2
else
2))
else
(if i.val < 2246 then
(if i.val < 2245 then
2
else
2)
else
(if i.val < 2247 then
2
else
2)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
2
else
2)
else
(if i.val < 2251 then
2
else
2))
else
(if i.val < 2254 then
(if i.val < 2253 then
2
else
2)
else
(if i.val < 2255 then
2
else
2))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
2
else
2)
else
(if i.val < 2259 then
2
else
2))
else
(if i.val < 2262 then
(if i.val < 2261 then
2
else
2)
else
(if i.val < 2263 then
2
else
2)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
2
else
2)
else
(if i.val < 2267 then
2
else
2))
else
(if i.val < 2270 then
(if i.val < 2269 then
2
else
2)
else
(if i.val < 2271 then
2
else
2)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
2
else
2)
else
(if i.val < 2275 then
2
else
2))
else
(if i.val < 2278 then
(if i.val < 2277 then
2
else
2)
else
(if i.val < 2279 then
2
else
1)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
2
else
2)
else
(if i.val < 2283 then
2
else
2))
else
(if i.val < 2286 then
(if i.val < 2285 then
2
else
2)
else
(if i.val < 2287 then
2
else
2))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
1
else
2)
else
(if i.val < 2291 then
2
else
2))
else
(if i.val < 2294 then
(if i.val < 2293 then
2
else
2)
else
(if i.val < 2295 then
2
else
2)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
2
else
2)
else
(if i.val < 2299 then
2
else
2))
else
(if i.val < 2302 then
(if i.val < 2301 then
2
else
2)
else
(if i.val < 2303 then
2
else
2))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
2
else
2)
else
(if i.val < 2307 then
2
else
2))
else
(if i.val < 2310 then
(if i.val < 2309 then
2
else
2)
else
(if i.val < 2311 then
2
else
2)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
2
else
2)
else
(if i.val < 2315 then
2
else
2))
else
(if i.val < 2318 then
(if i.val < 2317 then
2
else
2)
else
(if i.val < 2319 then
2
else
2))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
2
else
2)
else
(if i.val < 2323 then
2
else
2))
else
(if i.val < 2326 then
(if i.val < 2325 then
2
else
2)
else
(if i.val < 2327 then
2
else
2)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
2
else
1)
else
(if i.val < 2331 then
2
else
2))
else
(if i.val < 2334 then
(if i.val < 2333 then
2
else
2)
else
(if i.val < 2335 then
2
else
2)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
2
else
2)
else
(if i.val < 2339 then
2
else
2))
else
(if i.val < 2342 then
(if i.val < 2341 then
2
else
2)
else
(if i.val < 2343 then
2
else
2)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
2
else
2)
else
(if i.val < 2347 then
2
else
2))
else
(if i.val < 2350 then
(if i.val < 2349 then
2
else
2)
else
(if i.val < 2351 then
2
else
2))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
2
else
2)
else
(if i.val < 2355 then
2
else
2))
else
(if i.val < 2358 then
(if i.val < 2357 then
2
else
2)
else
(if i.val < 2359 then
2
else
2)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
2
else
2)
else
(if i.val < 2363 then
2
else
2))
else
(if i.val < 2366 then
(if i.val < 2365 then
2
else
2)
else
(if i.val < 2367 then
2
else
2))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
2
else
2)
else
(if i.val < 2371 then
2
else
2))
else
(if i.val < 2374 then
(if i.val < 2373 then
2
else
2)
else
(if i.val < 2375 then
2
else
2)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
2
else
2)
else
(if i.val < 2379 then
2
else
2))
else
(if i.val < 2382 then
(if i.val < 2381 then
2
else
2)
else
(if i.val < 2383 then
2
else
2))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
2
else
2)
else
(if i.val < 2387 then
2
else
2))
else
(if i.val < 2390 then
(if i.val < 2389 then
2
else
2)
else
(if i.val < 2391 then
2
else
2)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
2
else
2)
else
(if i.val < 2395 then
2
else
2))
else
(if i.val < 2398 then
(if i.val < 2397 then
2
else
2)
else
(if i.val < 2399 then
2
else
2)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
2
else
2)
else
(if i.val < 2403 then
2
else
2))
else
(if i.val < 2406 then
(if i.val < 2405 then
2
else
2)
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
2)
else
(if i.val < 2411 then
2
else
2))
else
(if i.val < 2414 then
(if i.val < 2413 then
2
else
2)
else
(if i.val < 2415 then
2
else
2))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
2
else
2)
else
(if i.val < 2419 then
2
else
2))
else
(if i.val < 2422 then
(if i.val < 2421 then
2
else
2)
else
(if i.val < 2423 then
2
else
2)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
2
else
2)
else
(if i.val < 2427 then
2
else
2))
else
(if i.val < 2430 then
(if i.val < 2429 then
2
else
2)
else
(if i.val < 2431 then
2
else
2)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
2
else
2)
else
(if i.val < 2435 then
2
else
2))
else
(if i.val < 2438 then
(if i.val < 2437 then
2
else
2)
else
(if i.val < 2439 then
2
else
2)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
2
else
2)
else
(if i.val < 2443 then
2
else
2))
else
(if i.val < 2446 then
(if i.val < 2445 then
2
else
2)
else
(if i.val < 2447 then
2
else
2))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
2
else
2)
else
(if i.val < 2451 then
2
else
2))
else
(if i.val < 2454 then
(if i.val < 2453 then
2
else
2)
else
(if i.val < 2455 then
2
else
2)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
2
else
2)
else
(if i.val < 2459 then
2
else
2))
else
(if i.val < 2462 then
(if i.val < 2461 then
2
else
2)
else
(if i.val < 2463 then
2
else
2)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
2
else
2)
else
(if i.val < 2467 then
2
else
2))
else
(if i.val < 2470 then
(if i.val < 2469 then
2
else
2)
else
(if i.val < 2471 then
2
else
2)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
2
else
2)
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
2)
else
(if i.val < 2479 then
2
else
2))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
2
else
2)
else
(if i.val < 2483 then
2
else
2))
else
(if i.val < 2486 then
(if i.val < 2485 then
2
else
2)
else
(if i.val < 2487 then
2
else
2)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
2
else
2)
else
(if i.val < 2491 then
2
else
2))
else
(if i.val < 2494 then
(if i.val < 2493 then
2
else
2)
else
(if i.val < 2495 then
2
else
2))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
2
else
2)
else
(if i.val < 2499 then
2
else
2))
else
(if i.val < 2502 then
(if i.val < 2501 then
2
else
2)
else
(if i.val < 2503 then
2
else
2)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
2
else
2)
else
(if i.val < 2507 then
2
else
2))
else
(if i.val < 2510 then
(if i.val < 2509 then
2
else
2)
else
(if i.val < 2511 then
2
else
2))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
2
else
2)
else
(if i.val < 2515 then
2
else
2))
else
(if i.val < 2518 then
(if i.val < 2517 then
2
else
2)
else
(if i.val < 2519 then
2
else
2)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
2
else
2)
else
(if i.val < 2523 then
2
else
2))
else
(if i.val < 2526 then
(if i.val < 2525 then
2
else
2)
else
(if i.val < 2527 then
2
else
2)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
2
else
2)
else
(if i.val < 2531 then
2
else
2))
else
(if i.val < 2534 then
(if i.val < 2533 then
2
else
2)
else
(if i.val < 2535 then
2
else
2)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
2
else
2)
else
(if i.val < 2539 then
2
else
2))
else
(if i.val < 2542 then
(if i.val < 2541 then
2
else
2)
else
(if i.val < 2543 then
2
else
2))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
2
else
2)
else
(if i.val < 2547 then
2
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
2
else
2)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
2
else
2)
else
(if i.val < 2555 then
2
else
2))
else
(if i.val < 2558 then
(if i.val < 2557 then
2
else
2)
else
(if i.val < 2559 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths2Part0005 : Fin 4368 → ℕ :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
2
else
2)
else
(if i.val < 2563 then
2
else
2))
else
(if i.val < 2566 then
(if i.val < 2565 then
2
else
2)
else
(if i.val < 2567 then
2
else
2)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
2
else
2)
else
(if i.val < 2571 then
2
else
2))
else
(if i.val < 2574 then
(if i.val < 2573 then
2
else
2)
else
(if i.val < 2575 then
2
else
2))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
2
else
2)
else
(if i.val < 2579 then
2
else
2))
else
(if i.val < 2582 then
(if i.val < 2581 then
2
else
2)
else
(if i.val < 2583 then
2
else
2)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
2
else
2)
else
(if i.val < 2587 then
2
else
2))
else
(if i.val < 2590 then
(if i.val < 2589 then
2
else
2)
else
(if i.val < 2591 then
2
else
2)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
2
else
2)
else
(if i.val < 2595 then
2
else
2))
else
(if i.val < 2598 then
(if i.val < 2597 then
2
else
2)
else
(if i.val < 2599 then
2
else
2)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
2
else
2)
else
(if i.val < 2603 then
2
else
2))
else
(if i.val < 2606 then
(if i.val < 2605 then
2
else
2)
else
(if i.val < 2607 then
2
else
2))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
2
else
2)
else
(if i.val < 2611 then
2
else
2))
else
(if i.val < 2614 then
(if i.val < 2613 then
2
else
2)
else
(if i.val < 2615 then
2
else
2)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
2
else
2)
else
(if i.val < 2619 then
2
else
2))
else
(if i.val < 2622 then
(if i.val < 2621 then
2
else
2)
else
(if i.val < 2623 then
2
else
1))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
2
else
2)
else
(if i.val < 2627 then
2
else
2))
else
(if i.val < 2630 then
(if i.val < 2629 then
2
else
2)
else
(if i.val < 2631 then
2
else
2)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
2
else
2)
else
(if i.val < 2635 then
2
else
2))
else
(if i.val < 2638 then
(if i.val < 2637 then
2
else
2)
else
(if i.val < 2639 then
2
else
2))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
2
else
2)
else
(if i.val < 2643 then
2
else
2))
else
(if i.val < 2646 then
(if i.val < 2645 then
2
else
2)
else
(if i.val < 2647 then
2
else
2)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
2
else
2)
else
(if i.val < 2651 then
2
else
1))
else
(if i.val < 2654 then
(if i.val < 2653 then
2
else
2)
else
(if i.val < 2655 then
2
else
2)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
2
else
2)
else
(if i.val < 2659 then
2
else
2))
else
(if i.val < 2662 then
(if i.val < 2661 then
2
else
2)
else
(if i.val < 2663 then
2
else
2)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
2
else
1)
else
(if i.val < 2667 then
2
else
2))
else
(if i.val < 2670 then
(if i.val < 2669 then
2
else
2)
else
(if i.val < 2671 then
2
else
2))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
2
else
2)
else
(if i.val < 2675 then
2
else
2))
else
(if i.val < 2678 then
(if i.val < 2677 then
2
else
2)
else
(if i.val < 2679 then
2
else
2)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
2
else
2)
else
(if i.val < 2683 then
2
else
2))
else
(if i.val < 2686 then
(if i.val < 2685 then
2
else
2)
else
(if i.val < 2687 then
2
else
2)))))))
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
2)
else
(if i.val < 2691 then
2
else
2))
else
(if i.val < 2694 then
(if i.val < 2693 then
2
else
2)
else
(if i.val < 2695 then
2
else
2)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
2
else
2)
else
(if i.val < 2699 then
2
else
2))
else
(if i.val < 2702 then
(if i.val < 2701 then
2
else
2)
else
(if i.val < 2703 then
2
else
2))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
2
else
2)
else
(if i.val < 2707 then
2
else
2))
else
(if i.val < 2710 then
(if i.val < 2709 then
2
else
2)
else
(if i.val < 2711 then
2
else
2)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
2
else
2)
else
(if i.val < 2715 then
2
else
2))
else
(if i.val < 2718 then
(if i.val < 2717 then
2
else
2)
else
(if i.val < 2719 then
2
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
2)
else
(if i.val < 2723 then
2
else
2))
else
(if i.val < 2726 then
(if i.val < 2725 then
2
else
2)
else
(if i.val < 2727 then
2
else
2)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
2
else
2)
else
(if i.val < 2731 then
2
else
2))
else
(if i.val < 2734 then
(if i.val < 2733 then
2
else
2)
else
(if i.val < 2735 then
2
else
2))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
2
else
2)
else
(if i.val < 2739 then
2
else
2))
else
(if i.val < 2742 then
(if i.val < 2741 then
2
else
2)
else
(if i.val < 2743 then
2
else
2)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
2
else
2)
else
(if i.val < 2747 then
2
else
2))
else
(if i.val < 2750 then
(if i.val < 2749 then
2
else
2)
else
(if i.val < 2751 then
2
else
2))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
2
else
2)
else
(if i.val < 2755 then
2
else
2))
else
(if i.val < 2758 then
(if i.val < 2757 then
2
else
2)
else
(if i.val < 2759 then
2
else
2)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
2
else
2)
else
(if i.val < 2763 then
2
else
2))
else
(if i.val < 2766 then
(if i.val < 2765 then
2
else
2)
else
(if i.val < 2767 then
2
else
2))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
2
else
1)
else
(if i.val < 2771 then
2
else
2))
else
(if i.val < 2774 then
(if i.val < 2773 then
2
else
2)
else
(if i.val < 2775 then
2
else
2)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
2
else
2)
else
(if i.val < 2779 then
2
else
2))
else
(if i.val < 2782 then
(if i.val < 2781 then
2
else
2)
else
(if i.val < 2783 then
2
else
2)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
2
else
2)
else
(if i.val < 2787 then
2
else
2))
else
(if i.val < 2790 then
(if i.val < 2789 then
2
else
2)
else
(if i.val < 2791 then
2
else
2)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
2
else
2)
else
(if i.val < 2795 then
2
else
2))
else
(if i.val < 2798 then
(if i.val < 2797 then
2
else
2)
else
(if i.val < 2799 then
2
else
2))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
2
else
2)
else
(if i.val < 2803 then
2
else
2))
else
(if i.val < 2806 then
(if i.val < 2805 then
2
else
2)
else
(if i.val < 2807 then
2
else
2)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
2
else
2)
else
(if i.val < 2811 then
2
else
2))
else
(if i.val < 2814 then
(if i.val < 2813 then
2
else
2)
else
(if i.val < 2815 then
2
else
2))))))))
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
2)
else
(if i.val < 2819 then
2
else
2))
else
(if i.val < 2822 then
(if i.val < 2821 then
2
else
2)
else
(if i.val < 2823 then
2
else
2)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
2
else
2)
else
(if i.val < 2827 then
2
else
2))
else
(if i.val < 2830 then
(if i.val < 2829 then
2
else
2)
else
(if i.val < 2831 then
2
else
2))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
2
else
2)
else
(if i.val < 2835 then
2
else
2))
else
(if i.val < 2838 then
(if i.val < 2837 then
2
else
2)
else
(if i.val < 2839 then
2
else
2)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
1
else
2)
else
(if i.val < 2843 then
2
else
1))
else
(if i.val < 2846 then
(if i.val < 2845 then
2
else
2)
else
(if i.val < 2847 then
2
else
2)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
2
else
2)
else
(if i.val < 2851 then
2
else
2))
else
(if i.val < 2854 then
(if i.val < 2853 then
2
else
2)
else
(if i.val < 2855 then
2
else
2)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
2
else
2)
else
(if i.val < 2859 then
2
else
2))
else
(if i.val < 2862 then
(if i.val < 2861 then
2
else
2)
else
(if i.val < 2863 then
2
else
2))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
2
else
2)
else
(if i.val < 2867 then
2
else
2))
else
(if i.val < 2870 then
(if i.val < 2869 then
2
else
2)
else
(if i.val < 2871 then
2
else
2)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
2
else
2)
else
(if i.val < 2875 then
2
else
2))
else
(if i.val < 2878 then
(if i.val < 2877 then
2
else
2)
else
(if i.val < 2879 then
2
else
2))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
2
else
2)
else
(if i.val < 2883 then
2
else
2))
else
(if i.val < 2886 then
(if i.val < 2885 then
2
else
1)
else
(if i.val < 2887 then
2
else
2)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
2
else
2)
else
(if i.val < 2891 then
2
else
2))
else
(if i.val < 2894 then
(if i.val < 2893 then
2
else
2)
else
(if i.val < 2895 then
2
else
2))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
2
else
2)
else
(if i.val < 2899 then
1
else
2))
else
(if i.val < 2902 then
(if i.val < 2901 then
2
else
2)
else
(if i.val < 2903 then
2
else
2)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
2
else
2)
else
(if i.val < 2907 then
2
else
2))
else
(if i.val < 2910 then
(if i.val < 2909 then
2
else
2)
else
(if i.val < 2911 then
2
else
2)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
2
else
2)
else
(if i.val < 2915 then
2
else
2))
else
(if i.val < 2918 then
(if i.val < 2917 then
2
else
2)
else
(if i.val < 2919 then
2
else
2)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
2
else
2)
else
(if i.val < 2923 then
2
else
2))
else
(if i.val < 2926 then
(if i.val < 2925 then
2
else
2)
else
(if i.val < 2927 then
2
else
2))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
2
else
2)
else
(if i.val < 2931 then
2
else
2))
else
(if i.val < 2934 then
(if i.val < 2933 then
2
else
2)
else
(if i.val < 2935 then
2
else
2)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
2
else
2)
else
(if i.val < 2939 then
2
else
2))
else
(if i.val < 2942 then
(if i.val < 2941 then
2
else
2)
else
(if i.val < 2943 then
2
else
2)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
2
else
2)
else
(if i.val < 2947 then
2
else
2))
else
(if i.val < 2950 then
(if i.val < 2949 then
2
else
2)
else
(if i.val < 2951 then
2
else
2)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
2
else
2)
else
(if i.val < 2955 then
2
else
2))
else
(if i.val < 2958 then
(if i.val < 2957 then
2
else
2)
else
(if i.val < 2959 then
2
else
2))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
2
else
2)
else
(if i.val < 2963 then
2
else
2))
else
(if i.val < 2966 then
(if i.val < 2965 then
2
else
2)
else
(if i.val < 2967 then
2
else
2)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
2
else
2)
else
(if i.val < 2971 then
2
else
2))
else
(if i.val < 2974 then
(if i.val < 2973 then
2
else
2)
else
(if i.val < 2975 then
2
else
2)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
2
else
2)
else
(if i.val < 2979 then
2
else
2))
else
(if i.val < 2982 then
(if i.val < 2981 then
2
else
2)
else
(if i.val < 2983 then
2
else
2)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
2
else
2)
else
(if i.val < 2987 then
2
else
2))
else
(if i.val < 2990 then
(if i.val < 2989 then
2
else
1)
else
(if i.val < 2991 then
2
else
2))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
2
else
2)
else
(if i.val < 2995 then
2
else
2))
else
(if i.val < 2998 then
(if i.val < 2997 then
2
else
2)
else
(if i.val < 2999 then
2
else
2)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
2
else
2)
else
(if i.val < 3003 then
2
else
2))
else
(if i.val < 3006 then
(if i.val < 3005 then
2
else
2)
else
(if i.val < 3007 then
2
else
2))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
2
else
2)
else
(if i.val < 3011 then
2
else
2))
else
(if i.val < 3014 then
(if i.val < 3013 then
2
else
2)
else
(if i.val < 3015 then
2
else
2)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
2
else
2)
else
(if i.val < 3019 then
2
else
2))
else
(if i.val < 3022 then
(if i.val < 3021 then
2
else
2)
else
(if i.val < 3023 then
2
else
2))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
1
else
2)
else
(if i.val < 3027 then
2
else
2))
else
(if i.val < 3030 then
(if i.val < 3029 then
2
else
2)
else
(if i.val < 3031 then
2
else
2)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
2
else
2)
else
(if i.val < 3035 then
2
else
2))
else
(if i.val < 3038 then
(if i.val < 3037 then
2
else
2)
else
(if i.val < 3039 then
2
else
2)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
2
else
2)
else
(if i.val < 3043 then
2
else
2))
else
(if i.val < 3046 then
(if i.val < 3045 then
2
else
2)
else
(if i.val < 3047 then
2
else
2)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
2
else
2)
else
(if i.val < 3051 then
2
else
1))
else
(if i.val < 3054 then
(if i.val < 3053 then
2
else
2)
else
(if i.val < 3055 then
2
else
2))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
2
else
2)
else
(if i.val < 3059 then
2
else
2))
else
(if i.val < 3062 then
(if i.val < 3061 then
2
else
2)
else
(if i.val < 3063 then
2
else
2)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
2
else
2)
else
(if i.val < 3067 then
2
else
2))
else
(if i.val < 3070 then
(if i.val < 3069 then
2
else
2)
else
(if i.val < 3071 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths2Part0006 : Fin 4368 → ℕ :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
2
else
2)
else
(if i.val < 3075 then
2
else
2))
else
(if i.val < 3078 then
(if i.val < 3077 then
2
else
2)
else
(if i.val < 3079 then
2
else
2)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
2
else
2)
else
(if i.val < 3083 then
2
else
2))
else
(if i.val < 3086 then
(if i.val < 3085 then
2
else
2)
else
(if i.val < 3087 then
2
else
1))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
2
else
2)
else
(if i.val < 3091 then
2
else
2))
else
(if i.val < 3094 then
(if i.val < 3093 then
2
else
2)
else
(if i.val < 3095 then
2
else
2)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
2
else
2)
else
(if i.val < 3099 then
2
else
2))
else
(if i.val < 3102 then
(if i.val < 3101 then
2
else
2)
else
(if i.val < 3103 then
2
else
2)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
2
else
2)
else
(if i.val < 3107 then
2
else
2))
else
(if i.val < 3110 then
(if i.val < 3109 then
2
else
2)
else
(if i.val < 3111 then
2
else
2)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
2
else
2)
else
(if i.val < 3115 then
2
else
2))
else
(if i.val < 3118 then
(if i.val < 3117 then
2
else
2)
else
(if i.val < 3119 then
2
else
2))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
2
else
2)
else
(if i.val < 3123 then
2
else
2))
else
(if i.val < 3126 then
(if i.val < 3125 then
2
else
2)
else
(if i.val < 3127 then
2
else
2)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
2
else
2)
else
(if i.val < 3131 then
2
else
2))
else
(if i.val < 3134 then
(if i.val < 3133 then
2
else
2)
else
(if i.val < 3135 then
1
else
2))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
2
else
2)
else
(if i.val < 3139 then
2
else
2))
else
(if i.val < 3142 then
(if i.val < 3141 then
2
else
2)
else
(if i.val < 3143 then
2
else
2)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
2
else
2)
else
(if i.val < 3147 then
2
else
2))
else
(if i.val < 3150 then
(if i.val < 3149 then
2
else
2)
else
(if i.val < 3151 then
2
else
2))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
2
else
2)
else
(if i.val < 3155 then
2
else
2))
else
(if i.val < 3158 then
(if i.val < 3157 then
2
else
2)
else
(if i.val < 3159 then
2
else
2)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
2
else
2)
else
(if i.val < 3163 then
2
else
2))
else
(if i.val < 3166 then
(if i.val < 3165 then
2
else
2)
else
(if i.val < 3167 then
2
else
2)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
2
else
2)
else
(if i.val < 3171 then
2
else
2))
else
(if i.val < 3174 then
(if i.val < 3173 then
2
else
2)
else
(if i.val < 3175 then
2
else
2)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
2
else
2)
else
(if i.val < 3179 then
2
else
2))
else
(if i.val < 3182 then
(if i.val < 3181 then
2
else
2)
else
(if i.val < 3183 then
2
else
2))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
2
else
1)
else
(if i.val < 3187 then
2
else
2))
else
(if i.val < 3190 then
(if i.val < 3189 then
2
else
2)
else
(if i.val < 3191 then
2
else
2)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
2
else
2)
else
(if i.val < 3195 then
2
else
2))
else
(if i.val < 3198 then
(if i.val < 3197 then
2
else
2)
else
(if i.val < 3199 then
2
else
2)))))))
else
(if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
2
else
2)
else
(if i.val < 3203 then
2
else
2))
else
(if i.val < 3206 then
(if i.val < 3205 then
2
else
2)
else
(if i.val < 3207 then
2
else
2)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
2
else
2)
else
(if i.val < 3211 then
2
else
2))
else
(if i.val < 3214 then
(if i.val < 3213 then
2
else
2)
else
(if i.val < 3215 then
2
else
2))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
2
else
2)
else
(if i.val < 3219 then
2
else
2))
else
(if i.val < 3222 then
(if i.val < 3221 then
2
else
2)
else
(if i.val < 3223 then
2
else
2)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
2
else
2)
else
(if i.val < 3227 then
2
else
2))
else
(if i.val < 3230 then
(if i.val < 3229 then
2
else
2)
else
(if i.val < 3231 then
2
else
2)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
2
else
2)
else
(if i.val < 3235 then
2
else
2))
else
(if i.val < 3238 then
(if i.val < 3237 then
2
else
2)
else
(if i.val < 3239 then
2
else
2)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
2
else
2)
else
(if i.val < 3243 then
2
else
2))
else
(if i.val < 3246 then
(if i.val < 3245 then
2
else
2)
else
(if i.val < 3247 then
2
else
2))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
2
else
2)
else
(if i.val < 3251 then
2
else
2))
else
(if i.val < 3254 then
(if i.val < 3253 then
2
else
2)
else
(if i.val < 3255 then
2
else
2)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
2
else
2)
else
(if i.val < 3259 then
2
else
2))
else
(if i.val < 3262 then
(if i.val < 3261 then
2
else
2)
else
(if i.val < 3263 then
2
else
2))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
2
else
2)
else
(if i.val < 3267 then
2
else
2))
else
(if i.val < 3270 then
(if i.val < 3269 then
2
else
2)
else
(if i.val < 3271 then
2
else
2)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
2
else
2)
else
(if i.val < 3275 then
2
else
2))
else
(if i.val < 3278 then
(if i.val < 3277 then
2
else
2)
else
(if i.val < 3279 then
2
else
2))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
2
else
2)
else
(if i.val < 3283 then
2
else
2))
else
(if i.val < 3286 then
(if i.val < 3285 then
2
else
2)
else
(if i.val < 3287 then
2
else
2)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
2
else
2)
else
(if i.val < 3291 then
2
else
2))
else
(if i.val < 3294 then
(if i.val < 3293 then
2
else
2)
else
(if i.val < 3295 then
2
else
2)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
2
else
2)
else
(if i.val < 3299 then
2
else
2))
else
(if i.val < 3302 then
(if i.val < 3301 then
2
else
2)
else
(if i.val < 3303 then
2
else
2)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
2
else
2)
else
(if i.val < 3307 then
2
else
2))
else
(if i.val < 3310 then
(if i.val < 3309 then
2
else
2)
else
(if i.val < 3311 then
2
else
2))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
2
else
2)
else
(if i.val < 3315 then
2
else
2))
else
(if i.val < 3318 then
(if i.val < 3317 then
2
else
2)
else
(if i.val < 3319 then
2
else
2)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
2
else
1)
else
(if i.val < 3323 then
2
else
2))
else
(if i.val < 3326 then
(if i.val < 3325 then
2
else
2)
else
(if i.val < 3327 then
2
else
2))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
2
else
2)
else
(if i.val < 3331 then
2
else
2))
else
(if i.val < 3334 then
(if i.val < 3333 then
1
else
2)
else
(if i.val < 3335 then
2
else
2)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
2
else
2)
else
(if i.val < 3339 then
2
else
2))
else
(if i.val < 3342 then
(if i.val < 3341 then
2
else
2)
else
(if i.val < 3343 then
2
else
2))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
2
else
2)
else
(if i.val < 3347 then
2
else
2))
else
(if i.val < 3350 then
(if i.val < 3349 then
2
else
2)
else
(if i.val < 3351 then
2
else
2)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
2
else
2)
else
(if i.val < 3355 then
2
else
2))
else
(if i.val < 3358 then
(if i.val < 3357 then
2
else
2)
else
(if i.val < 3359 then
2
else
2)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
2
else
2)
else
(if i.val < 3363 then
2
else
2))
else
(if i.val < 3366 then
(if i.val < 3365 then
2
else
2)
else
(if i.val < 3367 then
1
else
2)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
2
else
2)
else
(if i.val < 3371 then
2
else
2))
else
(if i.val < 3374 then
(if i.val < 3373 then
2
else
2)
else
(if i.val < 3375 then
2
else
2))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
2
else
2)
else
(if i.val < 3379 then
2
else
2))
else
(if i.val < 3382 then
(if i.val < 3381 then
2
else
2)
else
(if i.val < 3383 then
2
else
2)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
2
else
2)
else
(if i.val < 3387 then
2
else
2))
else
(if i.val < 3390 then
(if i.val < 3389 then
2
else
2)
else
(if i.val < 3391 then
2
else
2))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
2
else
2)
else
(if i.val < 3395 then
2
else
2))
else
(if i.val < 3398 then
(if i.val < 3397 then
2
else
2)
else
(if i.val < 3399 then
2
else
2)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
2
else
2)
else
(if i.val < 3403 then
2
else
2))
else
(if i.val < 3406 then
(if i.val < 3405 then
2
else
2)
else
(if i.val < 3407 then
2
else
2))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
2
else
2)
else
(if i.val < 3411 then
2
else
2))
else
(if i.val < 3414 then
(if i.val < 3413 then
2
else
2)
else
(if i.val < 3415 then
2
else
2)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
2
else
2)
else
(if i.val < 3419 then
2
else
2))
else
(if i.val < 3422 then
(if i.val < 3421 then
2
else
2)
else
(if i.val < 3423 then
2
else
2)))))
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
2
else
2))
else
(if i.val < 3430 then
(if i.val < 3429 then
2
else
2)
else
(if i.val < 3431 then
2
else
2)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
2
else
2)
else
(if i.val < 3435 then
2
else
2))
else
(if i.val < 3438 then
(if i.val < 3437 then
2
else
2)
else
(if i.val < 3439 then
2
else
2))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
2
else
2)
else
(if i.val < 3443 then
2
else
2))
else
(if i.val < 3446 then
(if i.val < 3445 then
2
else
2)
else
(if i.val < 3447 then
2
else
2)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
2
else
2)
else
(if i.val < 3451 then
2
else
2))
else
(if i.val < 3454 then
(if i.val < 3453 then
2
else
2)
else
(if i.val < 3455 then
2
else
2)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
2
else
2)
else
(if i.val < 3459 then
2
else
2))
else
(if i.val < 3462 then
(if i.val < 3461 then
2
else
2)
else
(if i.val < 3463 then
2
else
2)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
2
else
2)
else
(if i.val < 3467 then
2
else
2))
else
(if i.val < 3470 then
(if i.val < 3469 then
2
else
2)
else
(if i.val < 3471 then
2
else
2))))
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
2
else
2))
else
(if i.val < 3478 then
(if i.val < 3477 then
2
else
2)
else
(if i.val < 3479 then
2
else
2)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
2
else
2)
else
(if i.val < 3483 then
2
else
2))
else
(if i.val < 3486 then
(if i.val < 3485 then
2
else
2)
else
(if i.val < 3487 then
2
else
2)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
2
else
2)
else
(if i.val < 3491 then
2
else
2))
else
(if i.val < 3494 then
(if i.val < 3493 then
1
else
2)
else
(if i.val < 3495 then
1
else
1)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
2
else
2)
else
(if i.val < 3499 then
2
else
2))
else
(if i.val < 3502 then
(if i.val < 3501 then
2
else
2)
else
(if i.val < 3503 then
2
else
2))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
2
else
2)
else
(if i.val < 3507 then
2
else
2))
else
(if i.val < 3510 then
(if i.val < 3509 then
2
else
2)
else
(if i.val < 3511 then
1
else
2)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
2
else
2)
else
(if i.val < 3515 then
2
else
2))
else
(if i.val < 3518 then
(if i.val < 3517 then
2
else
2)
else
(if i.val < 3519 then
2
else
2))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
2
else
2)
else
(if i.val < 3523 then
2
else
2))
else
(if i.val < 3526 then
(if i.val < 3525 then
2
else
1)
else
(if i.val < 3527 then
2
else
2)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
2
else
2)
else
(if i.val < 3531 then
2
else
2))
else
(if i.val < 3534 then
(if i.val < 3533 then
2
else
2)
else
(if i.val < 3535 then
2
else
2))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
1
else
2)
else
(if i.val < 3539 then
2
else
1))
else
(if i.val < 3542 then
(if i.val < 3541 then
2
else
2)
else
(if i.val < 3543 then
2
else
2)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
2
else
2)
else
(if i.val < 3547 then
2
else
2))
else
(if i.val < 3550 then
(if i.val < 3549 then
2
else
2)
else
(if i.val < 3551 then
2
else
2)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
1
else
2)
else
(if i.val < 3555 then
2
else
2))
else
(if i.val < 3558 then
(if i.val < 3557 then
1
else
1)
else
(if i.val < 3559 then
2
else
2)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
2
else
2)
else
(if i.val < 3563 then
2
else
2))
else
(if i.val < 3566 then
(if i.val < 3565 then
2
else
2)
else
(if i.val < 3567 then
2
else
2))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
2
else
2)
else
(if i.val < 3571 then
2
else
2))
else
(if i.val < 3574 then
(if i.val < 3573 then
2
else
2)
else
(if i.val < 3575 then
2
else
2)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
2
else
2)
else
(if i.val < 3579 then
2
else
2))
else
(if i.val < 3582 then
(if i.val < 3581 then
2
else
2)
else
(if i.val < 3583 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths2Part0007 : Fin 4368 → ℕ :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
2
else
2)
else
(if i.val < 3587 then
2
else
1))
else
(if i.val < 3590 then
(if i.val < 3589 then
2
else
1)
else
(if i.val < 3591 then
2
else
2)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
2
else
2)
else
(if i.val < 3595 then
2
else
2))
else
(if i.val < 3598 then
(if i.val < 3597 then
1
else
2)
else
(if i.val < 3599 then
2
else
2))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
2
else
2)
else
(if i.val < 3603 then
2
else
2))
else
(if i.val < 3606 then
(if i.val < 3605 then
2
else
2)
else
(if i.val < 3607 then
2
else
2)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
2
else
2)
else
(if i.val < 3611 then
2
else
2))
else
(if i.val < 3614 then
(if i.val < 3613 then
2
else
2)
else
(if i.val < 3615 then
2
else
2)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
2
else
2)
else
(if i.val < 3619 then
2
else
2))
else
(if i.val < 3622 then
(if i.val < 3621 then
2
else
2)
else
(if i.val < 3623 then
2
else
2)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
1
else
1)
else
(if i.val < 3627 then
2
else
2))
else
(if i.val < 3630 then
(if i.val < 3629 then
2
else
2)
else
(if i.val < 3631 then
2
else
2))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
2
else
2)
else
(if i.val < 3635 then
2
else
2))
else
(if i.val < 3638 then
(if i.val < 3637 then
2
else
2)
else
(if i.val < 3639 then
2
else
2)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
2
else
2)
else
(if i.val < 3643 then
2
else
2))
else
(if i.val < 3646 then
(if i.val < 3645 then
2
else
2)
else
(if i.val < 3647 then
2
else
2))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
2
else
2)
else
(if i.val < 3651 then
2
else
2))
else
(if i.val < 3654 then
(if i.val < 3653 then
2
else
2)
else
(if i.val < 3655 then
2
else
2)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
2
else
2)
else
(if i.val < 3659 then
2
else
2))
else
(if i.val < 3662 then
(if i.val < 3661 then
2
else
2)
else
(if i.val < 3663 then
2
else
2))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
2
else
2)
else
(if i.val < 3667 then
2
else
2))
else
(if i.val < 3670 then
(if i.val < 3669 then
2
else
2)
else
(if i.val < 3671 then
2
else
2)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
2
else
2)
else
(if i.val < 3675 then
2
else
2))
else
(if i.val < 3678 then
(if i.val < 3677 then
2
else
2)
else
(if i.val < 3679 then
2
else
2)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
2
else
2)
else
(if i.val < 3683 then
2
else
1))
else
(if i.val < 3686 then
(if i.val < 3685 then
2
else
2)
else
(if i.val < 3687 then
2
else
2)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
2
else
2)
else
(if i.val < 3691 then
2
else
2))
else
(if i.val < 3694 then
(if i.val < 3693 then
2
else
2)
else
(if i.val < 3695 then
2
else
2))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
2
else
2)
else
(if i.val < 3699 then
2
else
2))
else
(if i.val < 3702 then
(if i.val < 3701 then
2
else
2)
else
(if i.val < 3703 then
2
else
2)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
2
else
2)
else
(if i.val < 3707 then
2
else
2))
else
(if i.val < 3710 then
(if i.val < 3709 then
2
else
2)
else
(if i.val < 3711 then
2
else
2)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
2
else
2)
else
(if i.val < 3715 then
2
else
2))
else
(if i.val < 3718 then
(if i.val < 3717 then
2
else
2)
else
(if i.val < 3719 then
2
else
2)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
2
else
2)
else
(if i.val < 3723 then
2
else
1))
else
(if i.val < 3726 then
(if i.val < 3725 then
2
else
2)
else
(if i.val < 3727 then
2
else
2))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
2
else
2)
else
(if i.val < 3731 then
2
else
2))
else
(if i.val < 3734 then
(if i.val < 3733 then
2
else
2)
else
(if i.val < 3735 then
2
else
2)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
2
else
2)
else
(if i.val < 3739 then
2
else
2))
else
(if i.val < 3742 then
(if i.val < 3741 then
2
else
2)
else
(if i.val < 3743 then
2
else
2)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
2
else
2)
else
(if i.val < 3747 then
2
else
2))
else
(if i.val < 3750 then
(if i.val < 3749 then
2
else
2)
else
(if i.val < 3751 then
2
else
2)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
2
else
2)
else
(if i.val < 3755 then
2
else
2))
else
(if i.val < 3758 then
(if i.val < 3757 then
2
else
1)
else
(if i.val < 3759 then
2
else
2))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
2
else
2)
else
(if i.val < 3763 then
2
else
2))
else
(if i.val < 3766 then
(if i.val < 3765 then
2
else
2)
else
(if i.val < 3767 then
2
else
2)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
2
else
1)
else
(if i.val < 3771 then
2
else
2))
else
(if i.val < 3774 then
(if i.val < 3773 then
2
else
2)
else
(if i.val < 3775 then
2
else
2))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
2
else
2)
else
(if i.val < 3779 then
2
else
2))
else
(if i.val < 3782 then
(if i.val < 3781 then
2
else
2)
else
(if i.val < 3783 then
2
else
2)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
2
else
2)
else
(if i.val < 3787 then
2
else
2))
else
(if i.val < 3790 then
(if i.val < 3789 then
2
else
2)
else
(if i.val < 3791 then
2
else
2))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
2
else
2)
else
(if i.val < 3795 then
2
else
2))
else
(if i.val < 3798 then
(if i.val < 3797 then
2
else
2)
else
(if i.val < 3799 then
2
else
2)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
2
else
2)
else
(if i.val < 3803 then
2
else
2))
else
(if i.val < 3806 then
(if i.val < 3805 then
2
else
2)
else
(if i.val < 3807 then
2
else
2)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
2
else
2)
else
(if i.val < 3811 then
2
else
2))
else
(if i.val < 3814 then
(if i.val < 3813 then
2
else
2)
else
(if i.val < 3815 then
2
else
2)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
2
else
2)
else
(if i.val < 3819 then
2
else
2))
else
(if i.val < 3822 then
(if i.val < 3821 then
2
else
2)
else
(if i.val < 3823 then
2
else
2))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
2
else
2)
else
(if i.val < 3827 then
2
else
2))
else
(if i.val < 3830 then
(if i.val < 3829 then
2
else
2)
else
(if i.val < 3831 then
2
else
2)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
2
else
2)
else
(if i.val < 3835 then
2
else
2))
else
(if i.val < 3838 then
(if i.val < 3837 then
2
else
2)
else
(if i.val < 3839 then
2
else
2))))))))
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
2)
else
(if i.val < 3843 then
2
else
1))
else
(if i.val < 3846 then
(if i.val < 3845 then
2
else
2)
else
(if i.val < 3847 then
2
else
2)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
2
else
2)
else
(if i.val < 3851 then
2
else
2))
else
(if i.val < 3854 then
(if i.val < 3853 then
1
else
2)
else
(if i.val < 3855 then
2
else
2))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
2
else
2)
else
(if i.val < 3859 then
2
else
2))
else
(if i.val < 3862 then
(if i.val < 3861 then
2
else
2)
else
(if i.val < 3863 then
2
else
2)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
2
else
1)
else
(if i.val < 3867 then
2
else
2))
else
(if i.val < 3870 then
(if i.val < 3869 then
2
else
2)
else
(if i.val < 3871 then
2
else
1)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
2
else
2)
else
(if i.val < 3875 then
2
else
2))
else
(if i.val < 3878 then
(if i.val < 3877 then
2
else
2)
else
(if i.val < 3879 then
2
else
2)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
2
else
2)
else
(if i.val < 3883 then
2
else
2))
else
(if i.val < 3886 then
(if i.val < 3885 then
2
else
2)
else
(if i.val < 3887 then
2
else
2))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
2
else
2)
else
(if i.val < 3891 then
2
else
2))
else
(if i.val < 3894 then
(if i.val < 3893 then
2
else
2)
else
(if i.val < 3895 then
2
else
2)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
2
else
2)
else
(if i.val < 3899 then
2
else
2))
else
(if i.val < 3902 then
(if i.val < 3901 then
2
else
2)
else
(if i.val < 3903 then
2
else
2))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
1
else
2)
else
(if i.val < 3907 then
2
else
2))
else
(if i.val < 3910 then
(if i.val < 3909 then
2
else
2)
else
(if i.val < 3911 then
2
else
2)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
2
else
2)
else
(if i.val < 3915 then
2
else
2))
else
(if i.val < 3918 then
(if i.val < 3917 then
2
else
2)
else
(if i.val < 3919 then
2
else
2))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
2
else
2)
else
(if i.val < 3923 then
2
else
2))
else
(if i.val < 3926 then
(if i.val < 3925 then
2
else
2)
else
(if i.val < 3927 then
2
else
2)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
2
else
2)
else
(if i.val < 3931 then
2
else
2))
else
(if i.val < 3934 then
(if i.val < 3933 then
2
else
2)
else
(if i.val < 3935 then
2
else
2)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
2
else
2)
else
(if i.val < 3939 then
2
else
2))
else
(if i.val < 3942 then
(if i.val < 3941 then
2
else
2)
else
(if i.val < 3943 then
2
else
2)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
2
else
2)
else
(if i.val < 3947 then
2
else
2))
else
(if i.val < 3950 then
(if i.val < 3949 then
2
else
2)
else
(if i.val < 3951 then
2
else
2))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
2
else
2)
else
(if i.val < 3955 then
2
else
2))
else
(if i.val < 3958 then
(if i.val < 3957 then
2
else
2)
else
(if i.val < 3959 then
2
else
2)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
2
else
2)
else
(if i.val < 3963 then
2
else
2))
else
(if i.val < 3966 then
(if i.val < 3965 then
2
else
2)
else
(if i.val < 3967 then
2
else
2)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
2
else
2)
else
(if i.val < 3971 then
2
else
2))
else
(if i.val < 3974 then
(if i.val < 3973 then
2
else
2)
else
(if i.val < 3975 then
2
else
2)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
2
else
2)
else
(if i.val < 3979 then
2
else
2))
else
(if i.val < 3982 then
(if i.val < 3981 then
2
else
2)
else
(if i.val < 3983 then
2
else
2))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
2
else
2)
else
(if i.val < 3987 then
2
else
2))
else
(if i.val < 3990 then
(if i.val < 3989 then
2
else
2)
else
(if i.val < 3991 then
1
else
2)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
2
else
2)
else
(if i.val < 3995 then
2
else
2))
else
(if i.val < 3998 then
(if i.val < 3997 then
2
else
1)
else
(if i.val < 3999 then
2
else
2)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
2
else
2)
else
(if i.val < 4003 then
2
else
2))
else
(if i.val < 4006 then
(if i.val < 4005 then
2
else
2)
else
(if i.val < 4007 then
2
else
2)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
2
else
2)
else
(if i.val < 4011 then
2
else
2))
else
(if i.val < 4014 then
(if i.val < 4013 then
2
else
2)
else
(if i.val < 4015 then
2
else
2))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
2
else
2)
else
(if i.val < 4019 then
2
else
2))
else
(if i.val < 4022 then
(if i.val < 4021 then
2
else
2)
else
(if i.val < 4023 then
2
else
2)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
2
else
2)
else
(if i.val < 4027 then
2
else
2))
else
(if i.val < 4030 then
(if i.val < 4029 then
2
else
2)
else
(if i.val < 4031 then
2
else
2))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
2
else
2)
else
(if i.val < 4035 then
2
else
2))
else
(if i.val < 4038 then
(if i.val < 4037 then
2
else
2)
else
(if i.val < 4039 then
2
else
2)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
2
else
2)
else
(if i.val < 4043 then
2
else
2))
else
(if i.val < 4046 then
(if i.val < 4045 then
2
else
2)
else
(if i.val < 4047 then
2
else
2))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
2
else
2)
else
(if i.val < 4051 then
2
else
2))
else
(if i.val < 4054 then
(if i.val < 4053 then
2
else
2)
else
(if i.val < 4055 then
2
else
2)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
2
else
2)
else
(if i.val < 4059 then
2
else
2))
else
(if i.val < 4062 then
(if i.val < 4061 then
2
else
2)
else
(if i.val < 4063 then
2
else
2)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
1
else
2)
else
(if i.val < 4067 then
2
else
2))
else
(if i.val < 4070 then
(if i.val < 4069 then
1
else
2)
else
(if i.val < 4071 then
2
else
2)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
2
else
2)
else
(if i.val < 4075 then
2
else
2))
else
(if i.val < 4078 then
(if i.val < 4077 then
2
else
2)
else
(if i.val < 4079 then
2
else
2))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
2
else
1)
else
(if i.val < 4083 then
2
else
2))
else
(if i.val < 4086 then
(if i.val < 4085 then
2
else
2)
else
(if i.val < 4087 then
2
else
2)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
2
else
2)
else
(if i.val < 4091 then
2
else
2))
else
(if i.val < 4094 then
(if i.val < 4093 then
2
else
2)
else
(if i.val < 4095 then
2
else
2)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetLengths2Part0008 : Fin 4368 → ℕ :=
  fun i => (if i.val < 4232 then
(if i.val < 4164 then
(if i.val < 4130 then
(if i.val < 4113 then
(if i.val < 4104 then
(if i.val < 4100 then
(if i.val < 4098 then
(if i.val < 4097 then
2
else
2)
else
(if i.val < 4099 then
2
else
1))
else
(if i.val < 4102 then
(if i.val < 4101 then
2
else
2)
else
(if i.val < 4103 then
2
else
2)))
else
(if i.val < 4108 then
(if i.val < 4106 then
(if i.val < 4105 then
2
else
2)
else
(if i.val < 4107 then
2
else
2))
else
(if i.val < 4110 then
(if i.val < 4109 then
2
else
2)
else
(if i.val < 4111 then
2
else
(if i.val < 4112 then
2
else
2)))))
else
(if i.val < 4121 then
(if i.val < 4117 then
(if i.val < 4115 then
(if i.val < 4114 then
2
else
2)
else
(if i.val < 4116 then
2
else
2))
else
(if i.val < 4119 then
(if i.val < 4118 then
2
else
2)
else
(if i.val < 4120 then
2
else
2)))
else
(if i.val < 4125 then
(if i.val < 4123 then
(if i.val < 4122 then
2
else
2)
else
(if i.val < 4124 then
2
else
2))
else
(if i.val < 4127 then
(if i.val < 4126 then
2
else
2)
else
(if i.val < 4128 then
2
else
(if i.val < 4129 then
2
else
2))))))
else
(if i.val < 4147 then
(if i.val < 4138 then
(if i.val < 4134 then
(if i.val < 4132 then
(if i.val < 4131 then
2
else
2)
else
(if i.val < 4133 then
2
else
2))
else
(if i.val < 4136 then
(if i.val < 4135 then
2
else
2)
else
(if i.val < 4137 then
2
else
2)))
else
(if i.val < 4142 then
(if i.val < 4140 then
(if i.val < 4139 then
2
else
2)
else
(if i.val < 4141 then
2
else
2))
else
(if i.val < 4144 then
(if i.val < 4143 then
1
else
2)
else
(if i.val < 4145 then
2
else
(if i.val < 4146 then
2
else
2)))))
else
(if i.val < 4155 then
(if i.val < 4151 then
(if i.val < 4149 then
(if i.val < 4148 then
2
else
2)
else
(if i.val < 4150 then
2
else
2))
else
(if i.val < 4153 then
(if i.val < 4152 then
2
else
2)
else
(if i.val < 4154 then
2
else
2)))
else
(if i.val < 4159 then
(if i.val < 4157 then
(if i.val < 4156 then
2
else
2)
else
(if i.val < 4158 then
2
else
2))
else
(if i.val < 4161 then
(if i.val < 4160 then
2
else
2)
else
(if i.val < 4162 then
2
else
(if i.val < 4163 then
2
else
2)))))))
else
(if i.val < 4198 then
(if i.val < 4181 then
(if i.val < 4172 then
(if i.val < 4168 then
(if i.val < 4166 then
(if i.val < 4165 then
2
else
2)
else
(if i.val < 4167 then
2
else
2))
else
(if i.val < 4170 then
(if i.val < 4169 then
2
else
1)
else
(if i.val < 4171 then
2
else
1)))
else
(if i.val < 4176 then
(if i.val < 4174 then
(if i.val < 4173 then
2
else
2)
else
(if i.val < 4175 then
2
else
2))
else
(if i.val < 4178 then
(if i.val < 4177 then
2
else
2)
else
(if i.val < 4179 then
2
else
(if i.val < 4180 then
2
else
2)))))
else
(if i.val < 4189 then
(if i.val < 4185 then
(if i.val < 4183 then
(if i.val < 4182 then
2
else
2)
else
(if i.val < 4184 then
2
else
2))
else
(if i.val < 4187 then
(if i.val < 4186 then
2
else
2)
else
(if i.val < 4188 then
2
else
2)))
else
(if i.val < 4193 then
(if i.val < 4191 then
(if i.val < 4190 then
2
else
2)
else
(if i.val < 4192 then
2
else
2))
else
(if i.val < 4195 then
(if i.val < 4194 then
2
else
2)
else
(if i.val < 4196 then
2
else
(if i.val < 4197 then
2
else
2))))))
else
(if i.val < 4215 then
(if i.val < 4206 then
(if i.val < 4202 then
(if i.val < 4200 then
(if i.val < 4199 then
2
else
2)
else
(if i.val < 4201 then
1
else
2))
else
(if i.val < 4204 then
(if i.val < 4203 then
2
else
1)
else
(if i.val < 4205 then
2
else
2)))
else
(if i.val < 4210 then
(if i.val < 4208 then
(if i.val < 4207 then
2
else
2)
else
(if i.val < 4209 then
2
else
2))
else
(if i.val < 4212 then
(if i.val < 4211 then
1
else
2)
else
(if i.val < 4213 then
2
else
(if i.val < 4214 then
1
else
2)))))
else
(if i.val < 4223 then
(if i.val < 4219 then
(if i.val < 4217 then
(if i.val < 4216 then
2
else
2)
else
(if i.val < 4218 then
2
else
2))
else
(if i.val < 4221 then
(if i.val < 4220 then
2
else
2)
else
(if i.val < 4222 then
2
else
2)))
else
(if i.val < 4227 then
(if i.val < 4225 then
(if i.val < 4224 then
2
else
2)
else
(if i.val < 4226 then
2
else
2))
else
(if i.val < 4229 then
(if i.val < 4228 then
2
else
2)
else
(if i.val < 4230 then
2
else
(if i.val < 4231 then
2
else
2))))))))
else
(if i.val < 4300 then
(if i.val < 4266 then
(if i.val < 4249 then
(if i.val < 4240 then
(if i.val < 4236 then
(if i.val < 4234 then
(if i.val < 4233 then
2
else
2)
else
(if i.val < 4235 then
2
else
2))
else
(if i.val < 4238 then
(if i.val < 4237 then
2
else
2)
else
(if i.val < 4239 then
1
else
2)))
else
(if i.val < 4244 then
(if i.val < 4242 then
(if i.val < 4241 then
2
else
2)
else
(if i.val < 4243 then
2
else
2))
else
(if i.val < 4246 then
(if i.val < 4245 then
2
else
2)
else
(if i.val < 4247 then
2
else
(if i.val < 4248 then
2
else
2)))))
else
(if i.val < 4257 then
(if i.val < 4253 then
(if i.val < 4251 then
(if i.val < 4250 then
2
else
2)
else
(if i.val < 4252 then
2
else
2))
else
(if i.val < 4255 then
(if i.val < 4254 then
1
else
2)
else
(if i.val < 4256 then
2
else
2)))
else
(if i.val < 4261 then
(if i.val < 4259 then
(if i.val < 4258 then
2
else
2)
else
(if i.val < 4260 then
2
else
2))
else
(if i.val < 4263 then
(if i.val < 4262 then
2
else
1)
else
(if i.val < 4264 then
1
else
(if i.val < 4265 then
2
else
2))))))
else
(if i.val < 4283 then
(if i.val < 4274 then
(if i.val < 4270 then
(if i.val < 4268 then
(if i.val < 4267 then
2
else
2)
else
(if i.val < 4269 then
2
else
2))
else
(if i.val < 4272 then
(if i.val < 4271 then
2
else
2)
else
(if i.val < 4273 then
2
else
1)))
else
(if i.val < 4278 then
(if i.val < 4276 then
(if i.val < 4275 then
1
else
2)
else
(if i.val < 4277 then
2
else
1))
else
(if i.val < 4280 then
(if i.val < 4279 then
2
else
2)
else
(if i.val < 4281 then
2
else
(if i.val < 4282 then
2
else
2)))))
else
(if i.val < 4291 then
(if i.val < 4287 then
(if i.val < 4285 then
(if i.val < 4284 then
2
else
2)
else
(if i.val < 4286 then
2
else
2))
else
(if i.val < 4289 then
(if i.val < 4288 then
2
else
2)
else
(if i.val < 4290 then
1
else
2)))
else
(if i.val < 4295 then
(if i.val < 4293 then
(if i.val < 4292 then
2
else
2)
else
(if i.val < 4294 then
2
else
2))
else
(if i.val < 4297 then
(if i.val < 4296 then
2
else
2)
else
(if i.val < 4298 then
2
else
(if i.val < 4299 then
2
else
1)))))))
else
(if i.val < 4334 then
(if i.val < 4317 then
(if i.val < 4308 then
(if i.val < 4304 then
(if i.val < 4302 then
(if i.val < 4301 then
2
else
2)
else
(if i.val < 4303 then
2
else
2))
else
(if i.val < 4306 then
(if i.val < 4305 then
2
else
2)
else
(if i.val < 4307 then
2
else
2)))
else
(if i.val < 4312 then
(if i.val < 4310 then
(if i.val < 4309 then
2
else
2)
else
(if i.val < 4311 then
2
else
2))
else
(if i.val < 4314 then
(if i.val < 4313 then
2
else
2)
else
(if i.val < 4315 then
2
else
(if i.val < 4316 then
2
else
1)))))
else
(if i.val < 4325 then
(if i.val < 4321 then
(if i.val < 4319 then
(if i.val < 4318 then
2
else
2)
else
(if i.val < 4320 then
2
else
2))
else
(if i.val < 4323 then
(if i.val < 4322 then
2
else
2)
else
(if i.val < 4324 then
1
else
2)))
else
(if i.val < 4329 then
(if i.val < 4327 then
(if i.val < 4326 then
2
else
2)
else
(if i.val < 4328 then
2
else
2))
else
(if i.val < 4331 then
(if i.val < 4330 then
2
else
2)
else
(if i.val < 4332 then
2
else
(if i.val < 4333 then
2
else
2))))))
else
(if i.val < 4351 then
(if i.val < 4342 then
(if i.val < 4338 then
(if i.val < 4336 then
(if i.val < 4335 then
2
else
1)
else
(if i.val < 4337 then
2
else
2))
else
(if i.val < 4340 then
(if i.val < 4339 then
2
else
2)
else
(if i.val < 4341 then
1
else
2)))
else
(if i.val < 4346 then
(if i.val < 4344 then
(if i.val < 4343 then
2
else
2)
else
(if i.val < 4345 then
2
else
2))
else
(if i.val < 4348 then
(if i.val < 4347 then
2
else
2)
else
(if i.val < 4349 then
2
else
(if i.val < 4350 then
2
else
2)))))
else
(if i.val < 4359 then
(if i.val < 4355 then
(if i.val < 4353 then
(if i.val < 4352 then
2
else
2)
else
(if i.val < 4354 then
2
else
2))
else
(if i.val < 4357 then
(if i.val < 4356 then
2
else
1)
else
(if i.val < 4358 then
2
else
1)))
else
(if i.val < 4363 then
(if i.val < 4361 then
(if i.val < 4360 then
2
else
2)
else
(if i.val < 4362 then
2
else
1))
else
(if i.val < 4365 then
(if i.val < 4364 then
2
else
2)
else
(if i.val < 4366 then
1
else
(if i.val < 4367 then
2
else
1)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetMonodromies0Part0000 : Fin 2880 → Fin 18 :=
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

def g32p_row31_cosetMonodromies0Part0001 : Fin 2880 → Fin 18 :=
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
0)
else
(if i.val < 715 then
0
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
0
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
0
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
0)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
0
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
0
else
0)
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
0)
else
(if i.val < 751 then
0
else
0))))
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
0))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
0)
else
(if i.val < 759 then
0
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
0
else
0)
else
(if i.val < 763 then
0
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
0
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
0
else
0)
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
0
else
0)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
0)
else
(if i.val < 779 then
0
else
0))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
0)
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
0))
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
0
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
0
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
0)
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

def g32p_row31_cosetMonodromies0Part0002 : Fin 2880 → Fin 18 :=
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
0)))
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
0)
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
0)
else
(if i.val < 1155 then
0
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
0)
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
0)
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
0
else
0)
else
(if i.val < 1171 then
0
else
0))
else
(if i.val < 1174 then
(if i.val < 1173 then
0
else
0)
else
(if i.val < 1175 then
0
else
0)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
0
else
0)
else
(if i.val < 1179 then
0
else
0))
else
(if i.val < 1182 then
(if i.val < 1181 then
0
else
0)
else
(if i.val < 1183 then
0
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
0)
else
(if i.val < 1187 then
0
else
0))
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
0
else
0)
else
(if i.val < 1195 then
0
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
0)
else
(if i.val < 1203 then
0
else
0))
else
(if i.val < 1206 then
(if i.val < 1205 then
0
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
0
else
0)
else
(if i.val < 1211 then
0
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
0
else
0))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
0
else
0)
else
(if i.val < 1219 then
0
else
0))
else
(if i.val < 1222 then
(if i.val < 1221 then
0
else
0)
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
0)
else
(if i.val < 1227 then
0
else
0))
else
(if i.val < 1230 then
(if i.val < 1229 then
0
else
0)
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
0)
else
(if i.val < 1255 then
0
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
0
else
0))
else
(if i.val < 1270 then
(if i.val < 1269 then
0
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
0
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
0)
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
0
else
0))
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
0
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
0))
else
(if i.val < 1358 then
(if i.val < 1357 then
0
else
0)
else
(if i.val < 1359 then
0
else
0))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
0
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
0
else
0)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
0
else
0)
else
(if i.val < 1371 then
0
else
0))
else
(if i.val < 1374 then
(if i.val < 1373 then
0
else
0)
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
0
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
0
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
0)
else
(if i.val < 1407 then
0
else
0)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
0
else
0)
else
(if i.val < 1411 then
0
else
0))
else
(if i.val < 1414 then
(if i.val < 1413 then
0
else
0)
else
(if i.val < 1415 then
0
else
0)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
0
else
0)
else
(if i.val < 1419 then
0
else
0))
else
(if i.val < 1422 then
(if i.val < 1421 then
0
else
0)
else
(if i.val < 1423 then
0
else
0))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
0
else
0)
else
(if i.val < 1427 then
0
else
0))
else
(if i.val < 1430 then
(if i.val < 1429 then
0
else
0)
else
(if i.val < 1431 then
0
else
0)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
0
else
0)
else
(if i.val < 1435 then
0
else
0))
else
(if i.val < 1438 then
(if i.val < 1437 then
0
else
0)
else
(if i.val < 1439 then
0
else
0)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
0
else
0)
else
(if i.val < 1443 then
0
else
0))
else
(if i.val < 1446 then
(if i.val < 1445 then
0
else
0)
else
(if i.val < 1447 then
0
else
0)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
0
else
0)
else
(if i.val < 1451 then
0
else
0))
else
(if i.val < 1454 then
(if i.val < 1453 then
0
else
0)
else
(if i.val < 1455 then
0
else
0))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
0
else
0)
else
(if i.val < 1459 then
0
else
0))
else
(if i.val < 1462 then
(if i.val < 1461 then
0
else
0)
else
(if i.val < 1463 then
0
else
0)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
0
else
0)
else
(if i.val < 1467 then
0
else
0))
else
(if i.val < 1470 then
(if i.val < 1469 then
0
else
0)
else
(if i.val < 1471 then
0
else
0))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
0
else
0)
else
(if i.val < 1475 then
0
else
0))
else
(if i.val < 1478 then
(if i.val < 1477 then
0
else
0)
else
(if i.val < 1479 then
0
else
0)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
0
else
0)
else
(if i.val < 1483 then
0
else
0))
else
(if i.val < 1486 then
(if i.val < 1485 then
0
else
0)
else
(if i.val < 1487 then
0
else
0))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
0
else
0)
else
(if i.val < 1491 then
0
else
0))
else
(if i.val < 1494 then
(if i.val < 1493 then
0
else
0)
else
(if i.val < 1495 then
0
else
0)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
0
else
0)
else
(if i.val < 1499 then
0
else
0))
else
(if i.val < 1502 then
(if i.val < 1501 then
0
else
0)
else
(if i.val < 1503 then
0
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
0)
else
(if i.val < 1507 then
0
else
0))
else
(if i.val < 1510 then
(if i.val < 1509 then
0
else
0)
else
(if i.val < 1511 then
0
else
0)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
0
else
0)
else
(if i.val < 1515 then
0
else
0))
else
(if i.val < 1518 then
(if i.val < 1517 then
0
else
0)
else
(if i.val < 1519 then
0
else
0))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
0
else
0)
else
(if i.val < 1523 then
0
else
0))
else
(if i.val < 1526 then
(if i.val < 1525 then
0
else
0)
else
(if i.val < 1527 then
0
else
0)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
0
else
0)
else
(if i.val < 1531 then
0
else
0))
else
(if i.val < 1534 then
(if i.val < 1533 then
0
else
0)
else
(if i.val < 1535 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetMonodromies0Part0003 : Fin 2880 → Fin 18 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
0
else
0)
else
(if i.val < 1539 then
0
else
0))
else
(if i.val < 1542 then
(if i.val < 1541 then
0
else
0)
else
(if i.val < 1543 then
0
else
0)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
0
else
0)
else
(if i.val < 1547 then
0
else
0))
else
(if i.val < 1550 then
(if i.val < 1549 then
0
else
0)
else
(if i.val < 1551 then
0
else
0))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
0
else
0)
else
(if i.val < 1555 then
0
else
0))
else
(if i.val < 1558 then
(if i.val < 1557 then
0
else
0)
else
(if i.val < 1559 then
0
else
0)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
0
else
0)
else
(if i.val < 1563 then
0
else
0))
else
(if i.val < 1566 then
(if i.val < 1565 then
0
else
0)
else
(if i.val < 1567 then
0
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
0)
else
(if i.val < 1571 then
0
else
0))
else
(if i.val < 1574 then
(if i.val < 1573 then
0
else
0)
else
(if i.val < 1575 then
0
else
0)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
0
else
0)
else
(if i.val < 1579 then
0
else
0))
else
(if i.val < 1582 then
(if i.val < 1581 then
0
else
0)
else
(if i.val < 1583 then
0
else
0))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
0
else
0)
else
(if i.val < 1587 then
0
else
0))
else
(if i.val < 1590 then
(if i.val < 1589 then
0
else
0)
else
(if i.val < 1591 then
0
else
0)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
0
else
0)
else
(if i.val < 1595 then
0
else
0))
else
(if i.val < 1598 then
(if i.val < 1597 then
0
else
0)
else
(if i.val < 1599 then
0
else
0))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
0
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
0
else
0)
else
(if i.val < 1607 then
0
else
0)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
0
else
0)
else
(if i.val < 1611 then
0
else
0))
else
(if i.val < 1614 then
(if i.val < 1613 then
0
else
0)
else
(if i.val < 1615 then
0
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
0
else
0))
else
(if i.val < 1622 then
(if i.val < 1621 then
0
else
0)
else
(if i.val < 1623 then
0
else
0)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
0
else
0)
else
(if i.val < 1627 then
0
else
0))
else
(if i.val < 1630 then
(if i.val < 1629 then
0
else
0)
else
(if i.val < 1631 then
0
else
0)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
0
else
0)
else
(if i.val < 1635 then
0
else
0))
else
(if i.val < 1638 then
(if i.val < 1637 then
0
else
0)
else
(if i.val < 1639 then
0
else
0)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
0
else
0)
else
(if i.val < 1643 then
0
else
0))
else
(if i.val < 1646 then
(if i.val < 1645 then
0
else
0)
else
(if i.val < 1647 then
0
else
0))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
0
else
0)
else
(if i.val < 1651 then
0
else
0))
else
(if i.val < 1654 then
(if i.val < 1653 then
0
else
0)
else
(if i.val < 1655 then
0
else
0)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
0
else
0)
else
(if i.val < 1659 then
0
else
0))
else
(if i.val < 1662 then
(if i.val < 1661 then
0
else
0)
else
(if i.val < 1663 then
0
else
0)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
0
else
0)
else
(if i.val < 1667 then
0
else
0))
else
(if i.val < 1670 then
(if i.val < 1669 then
0
else
0)
else
(if i.val < 1671 then
0
else
0)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
0
else
0)
else
(if i.val < 1675 then
0
else
0))
else
(if i.val < 1678 then
(if i.val < 1677 then
0
else
0)
else
(if i.val < 1679 then
0
else
0))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
0
else
0)
else
(if i.val < 1683 then
0
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
0
else
0)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
0
else
0)
else
(if i.val < 1691 then
0
else
0))
else
(if i.val < 1694 then
(if i.val < 1693 then
0
else
0)
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
0)
else
(if i.val < 1699 then
0
else
0))
else
(if i.val < 1702 then
(if i.val < 1701 then
0
else
0)
else
(if i.val < 1703 then
0
else
0)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
0
else
0)
else
(if i.val < 1707 then
0
else
0))
else
(if i.val < 1710 then
(if i.val < 1709 then
0
else
0)
else
(if i.val < 1711 then
0
else
0))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
0
else
0)
else
(if i.val < 1715 then
0
else
0))
else
(if i.val < 1718 then
(if i.val < 1717 then
0
else
0)
else
(if i.val < 1719 then
0
else
0)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
0
else
0)
else
(if i.val < 1723 then
0
else
0))
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
0
else
0)
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
0)
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
0)
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
0)))))
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
0)
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
0)))
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
0))
else
(if i.val < 1822 then
(if i.val < 1821 then
0
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
0
else
0)
else
(if i.val < 1827 then
0
else
0))
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
0
else
0)
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
0
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
0)
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
0
else
0))
else
(if i.val < 1854 then
(if i.val < 1853 then
0
else
0)
else
(if i.val < 1855 then
0
else
0))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
0
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
0)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
0
else
0)
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
0)
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
0))
else
(if i.val < 1878 then
(if i.val < 1877 then
0
else
0)
else
(if i.val < 1879 then
0
else
0)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
0
else
0)
else
(if i.val < 1883 then
0
else
0))
else
(if i.val < 1886 then
(if i.val < 1885 then
0
else
0)
else
(if i.val < 1887 then
0
else
0)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
0
else
0)
else
(if i.val < 1891 then
0
else
0))
else
(if i.val < 1894 then
(if i.val < 1893 then
0
else
0)
else
(if i.val < 1895 then
0
else
0)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
0
else
0)
else
(if i.val < 1899 then
0
else
0))
else
(if i.val < 1902 then
(if i.val < 1901 then
0
else
0)
else
(if i.val < 1903 then
0
else
0))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
0
else
0)
else
(if i.val < 1907 then
0
else
0))
else
(if i.val < 1910 then
(if i.val < 1909 then
0
else
0)
else
(if i.val < 1911 then
0
else
0)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
0
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
0
else
0)
else
(if i.val < 1919 then
0
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
0
else
0)
else
(if i.val < 1923 then
0
else
0))
else
(if i.val < 1926 then
(if i.val < 1925 then
0
else
0)
else
(if i.val < 1927 then
0
else
0)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
0
else
0)
else
(if i.val < 1931 then
0
else
0))
else
(if i.val < 1934 then
(if i.val < 1933 then
0
else
0)
else
(if i.val < 1935 then
0
else
0))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
0
else
0)
else
(if i.val < 1939 then
0
else
0))
else
(if i.val < 1942 then
(if i.val < 1941 then
0
else
0)
else
(if i.val < 1943 then
0
else
0)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
0
else
0)
else
(if i.val < 1947 then
0
else
0))
else
(if i.val < 1950 then
(if i.val < 1949 then
0
else
0)
else
(if i.val < 1951 then
0
else
0)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
0
else
0)
else
(if i.val < 1955 then
0
else
0))
else
(if i.val < 1958 then
(if i.val < 1957 then
0
else
0)
else
(if i.val < 1959 then
0
else
0)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
0
else
0)
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
0)
else
(if i.val < 1967 then
0
else
0))))
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
0
else
0))
else
(if i.val < 1974 then
(if i.val < 1973 then
0
else
0)
else
(if i.val < 1975 then
0
else
0)))
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
0))
else
(if i.val < 1982 then
(if i.val < 1981 then
0
else
0)
else
(if i.val < 1983 then
0
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
0)
else
(if i.val < 1987 then
0
else
0))
else
(if i.val < 1990 then
(if i.val < 1989 then
0
else
0)
else
(if i.val < 1991 then
0
else
0)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
0
else
0)
else
(if i.val < 1995 then
0
else
0))
else
(if i.val < 1998 then
(if i.val < 1997 then
0
else
0)
else
(if i.val < 1999 then
0
else
0))))
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

def g32p_row31_cosetMonodromies0Part0004 : Fin 2880 → Fin 18 :=
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
0)
else
(if i.val < 2303 then
0
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
0
else
0)
else
(if i.val < 2307 then
0
else
0))
else
(if i.val < 2310 then
(if i.val < 2309 then
0
else
0)
else
(if i.val < 2311 then
0
else
0)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
0
else
0)
else
(if i.val < 2315 then
0
else
0))
else
(if i.val < 2318 then
(if i.val < 2317 then
0
else
0)
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
0
else
0)
else
(if i.val < 2323 then
0
else
0))
else
(if i.val < 2326 then
(if i.val < 2325 then
0
else
0)
else
(if i.val < 2327 then
0
else
0)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
0
else
0)
else
(if i.val < 2331 then
0
else
0))
else
(if i.val < 2334 then
(if i.val < 2333 then
0
else
0)
else
(if i.val < 2335 then
0
else
0)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
0
else
0)
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
0
else
0)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
0
else
0)
else
(if i.val < 2347 then
0
else
0))
else
(if i.val < 2350 then
(if i.val < 2349 then
0
else
0)
else
(if i.val < 2351 then
0
else
0))))
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
0)
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
0)
else
(if i.val < 2363 then
0
else
0))
else
(if i.val < 2366 then
(if i.val < 2365 then
0
else
0)
else
(if i.val < 2367 then
0
else
0))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
0
else
0)
else
(if i.val < 2371 then
0
else
0))
else
(if i.val < 2374 then
(if i.val < 2373 then
0
else
0)
else
(if i.val < 2375 then
0
else
0)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
0
else
0)
else
(if i.val < 2379 then
0
else
0))
else
(if i.val < 2382 then
(if i.val < 2381 then
0
else
0)
else
(if i.val < 2383 then
0
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
0))
else
(if i.val < 2406 then
(if i.val < 2405 then
0
else
0)
else
(if i.val < 2407 then
0
else
0)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
0
else
0)
else
(if i.val < 2411 then
0
else
0))
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
0))))
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
0
else
0))
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
0)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
0
else
0)
else
(if i.val < 2427 then
0
else
0))
else
(if i.val < 2430 then
(if i.val < 2429 then
0
else
0)
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
0
else
0)
else
(if i.val < 2435 then
0
else
0))
else
(if i.val < 2438 then
(if i.val < 2437 then
0
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
0
else
0)
else
(if i.val < 2443 then
0
else
0))
else
(if i.val < 2446 then
(if i.val < 2445 then
0
else
0)
else
(if i.val < 2447 then
0
else
0))))
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
0
else
0))
else
(if i.val < 2454 then
(if i.val < 2453 then
0
else
0)
else
(if i.val < 2455 then
0
else
0)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
0
else
0)
else
(if i.val < 2459 then
0
else
0))
else
(if i.val < 2462 then
(if i.val < 2461 then
0
else
0)
else
(if i.val < 2463 then
0
else
0)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
0
else
0)
else
(if i.val < 2467 then
0
else
0))
else
(if i.val < 2470 then
(if i.val < 2469 then
0
else
0)
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
0
else
0))
else
(if i.val < 2478 then
(if i.val < 2477 then
0
else
0)
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
0
else
0)
else
(if i.val < 2483 then
0
else
0))
else
(if i.val < 2486 then
(if i.val < 2485 then
0
else
0)
else
(if i.val < 2487 then
0
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
0
else
0))
else
(if i.val < 2494 then
(if i.val < 2493 then
0
else
0)
else
(if i.val < 2495 then
0
else
0))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
0
else
0)
else
(if i.val < 2499 then
0
else
0))
else
(if i.val < 2502 then
(if i.val < 2501 then
0
else
0)
else
(if i.val < 2503 then
0
else
0)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
0
else
0)
else
(if i.val < 2507 then
0
else
0))
else
(if i.val < 2510 then
(if i.val < 2509 then
0
else
0)
else
(if i.val < 2511 then
0
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
0
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
0)
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
0)
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

def g32p_row31_cosetMonodromies0Part0005 : Fin 2880 → Fin 18 :=
  fun i => (if i.val < 2720 then
(if i.val < 2640 then
(if i.val < 2600 then
(if i.val < 2580 then
(if i.val < 2570 then
(if i.val < 2565 then
(if i.val < 2562 then
(if i.val < 2561 then
0
else
0)
else
(if i.val < 2563 then
0
else
(if i.val < 2564 then
0
else
0)))
else
(if i.val < 2567 then
(if i.val < 2566 then
0
else
0)
else
(if i.val < 2568 then
0
else
(if i.val < 2569 then
0
else
0))))
else
(if i.val < 2575 then
(if i.val < 2572 then
(if i.val < 2571 then
0
else
0)
else
(if i.val < 2573 then
0
else
(if i.val < 2574 then
0
else
0)))
else
(if i.val < 2577 then
(if i.val < 2576 then
0
else
0)
else
(if i.val < 2578 then
0
else
(if i.val < 2579 then
0
else
0)))))
else
(if i.val < 2590 then
(if i.val < 2585 then
(if i.val < 2582 then
(if i.val < 2581 then
0
else
0)
else
(if i.val < 2583 then
0
else
(if i.val < 2584 then
0
else
0)))
else
(if i.val < 2587 then
(if i.val < 2586 then
0
else
0)
else
(if i.val < 2588 then
0
else
(if i.val < 2589 then
0
else
0))))
else
(if i.val < 2595 then
(if i.val < 2592 then
(if i.val < 2591 then
0
else
0)
else
(if i.val < 2593 then
0
else
(if i.val < 2594 then
0
else
0)))
else
(if i.val < 2597 then
(if i.val < 2596 then
0
else
0)
else
(if i.val < 2598 then
0
else
(if i.val < 2599 then
0
else
0))))))
else
(if i.val < 2620 then
(if i.val < 2610 then
(if i.val < 2605 then
(if i.val < 2602 then
(if i.val < 2601 then
0
else
0)
else
(if i.val < 2603 then
0
else
(if i.val < 2604 then
0
else
0)))
else
(if i.val < 2607 then
(if i.val < 2606 then
0
else
0)
else
(if i.val < 2608 then
0
else
(if i.val < 2609 then
0
else
0))))
else
(if i.val < 2615 then
(if i.val < 2612 then
(if i.val < 2611 then
0
else
0)
else
(if i.val < 2613 then
0
else
(if i.val < 2614 then
0
else
0)))
else
(if i.val < 2617 then
(if i.val < 2616 then
0
else
0)
else
(if i.val < 2618 then
0
else
(if i.val < 2619 then
0
else
0)))))
else
(if i.val < 2630 then
(if i.val < 2625 then
(if i.val < 2622 then
(if i.val < 2621 then
0
else
0)
else
(if i.val < 2623 then
0
else
(if i.val < 2624 then
0
else
0)))
else
(if i.val < 2627 then
(if i.val < 2626 then
0
else
0)
else
(if i.val < 2628 then
0
else
(if i.val < 2629 then
0
else
0))))
else
(if i.val < 2635 then
(if i.val < 2632 then
(if i.val < 2631 then
0
else
0)
else
(if i.val < 2633 then
0
else
(if i.val < 2634 then
0
else
0)))
else
(if i.val < 2637 then
(if i.val < 2636 then
0
else
0)
else
(if i.val < 2638 then
0
else
(if i.val < 2639 then
0
else
0)))))))
else
(if i.val < 2680 then
(if i.val < 2660 then
(if i.val < 2650 then
(if i.val < 2645 then
(if i.val < 2642 then
(if i.val < 2641 then
0
else
0)
else
(if i.val < 2643 then
0
else
(if i.val < 2644 then
0
else
0)))
else
(if i.val < 2647 then
(if i.val < 2646 then
0
else
0)
else
(if i.val < 2648 then
0
else
(if i.val < 2649 then
0
else
0))))
else
(if i.val < 2655 then
(if i.val < 2652 then
(if i.val < 2651 then
0
else
0)
else
(if i.val < 2653 then
0
else
(if i.val < 2654 then
0
else
0)))
else
(if i.val < 2657 then
(if i.val < 2656 then
0
else
0)
else
(if i.val < 2658 then
0
else
(if i.val < 2659 then
0
else
0)))))
else
(if i.val < 2670 then
(if i.val < 2665 then
(if i.val < 2662 then
(if i.val < 2661 then
0
else
0)
else
(if i.val < 2663 then
0
else
(if i.val < 2664 then
0
else
0)))
else
(if i.val < 2667 then
(if i.val < 2666 then
0
else
0)
else
(if i.val < 2668 then
0
else
(if i.val < 2669 then
0
else
0))))
else
(if i.val < 2675 then
(if i.val < 2672 then
(if i.val < 2671 then
0
else
0)
else
(if i.val < 2673 then
0
else
(if i.val < 2674 then
0
else
0)))
else
(if i.val < 2677 then
(if i.val < 2676 then
0
else
0)
else
(if i.val < 2678 then
0
else
(if i.val < 2679 then
0
else
0))))))
else
(if i.val < 2700 then
(if i.val < 2690 then
(if i.val < 2685 then
(if i.val < 2682 then
(if i.val < 2681 then
0
else
0)
else
(if i.val < 2683 then
0
else
(if i.val < 2684 then
0
else
0)))
else
(if i.val < 2687 then
(if i.val < 2686 then
0
else
0)
else
(if i.val < 2688 then
0
else
(if i.val < 2689 then
0
else
0))))
else
(if i.val < 2695 then
(if i.val < 2692 then
(if i.val < 2691 then
0
else
0)
else
(if i.val < 2693 then
0
else
(if i.val < 2694 then
0
else
0)))
else
(if i.val < 2697 then
(if i.val < 2696 then
0
else
0)
else
(if i.val < 2698 then
0
else
(if i.val < 2699 then
0
else
0)))))
else
(if i.val < 2710 then
(if i.val < 2705 then
(if i.val < 2702 then
(if i.val < 2701 then
0
else
0)
else
(if i.val < 2703 then
0
else
(if i.val < 2704 then
0
else
0)))
else
(if i.val < 2707 then
(if i.val < 2706 then
0
else
0)
else
(if i.val < 2708 then
0
else
(if i.val < 2709 then
0
else
0))))
else
(if i.val < 2715 then
(if i.val < 2712 then
(if i.val < 2711 then
0
else
0)
else
(if i.val < 2713 then
0
else
(if i.val < 2714 then
0
else
0)))
else
(if i.val < 2717 then
(if i.val < 2716 then
0
else
0)
else
(if i.val < 2718 then
0
else
(if i.val < 2719 then
0
else
0))))))))
else
(if i.val < 2800 then
(if i.val < 2760 then
(if i.val < 2740 then
(if i.val < 2730 then
(if i.val < 2725 then
(if i.val < 2722 then
(if i.val < 2721 then
0
else
0)
else
(if i.val < 2723 then
0
else
(if i.val < 2724 then
0
else
0)))
else
(if i.val < 2727 then
(if i.val < 2726 then
0
else
0)
else
(if i.val < 2728 then
0
else
(if i.val < 2729 then
0
else
0))))
else
(if i.val < 2735 then
(if i.val < 2732 then
(if i.val < 2731 then
0
else
0)
else
(if i.val < 2733 then
0
else
(if i.val < 2734 then
0
else
0)))
else
(if i.val < 2737 then
(if i.val < 2736 then
0
else
0)
else
(if i.val < 2738 then
0
else
(if i.val < 2739 then
0
else
0)))))
else
(if i.val < 2750 then
(if i.val < 2745 then
(if i.val < 2742 then
(if i.val < 2741 then
0
else
0)
else
(if i.val < 2743 then
0
else
(if i.val < 2744 then
0
else
0)))
else
(if i.val < 2747 then
(if i.val < 2746 then
0
else
0)
else
(if i.val < 2748 then
0
else
(if i.val < 2749 then
0
else
0))))
else
(if i.val < 2755 then
(if i.val < 2752 then
(if i.val < 2751 then
0
else
0)
else
(if i.val < 2753 then
0
else
(if i.val < 2754 then
0
else
0)))
else
(if i.val < 2757 then
(if i.val < 2756 then
0
else
0)
else
(if i.val < 2758 then
0
else
(if i.val < 2759 then
0
else
0))))))
else
(if i.val < 2780 then
(if i.val < 2770 then
(if i.val < 2765 then
(if i.val < 2762 then
(if i.val < 2761 then
0
else
0)
else
(if i.val < 2763 then
0
else
(if i.val < 2764 then
0
else
0)))
else
(if i.val < 2767 then
(if i.val < 2766 then
0
else
0)
else
(if i.val < 2768 then
0
else
(if i.val < 2769 then
0
else
0))))
else
(if i.val < 2775 then
(if i.val < 2772 then
(if i.val < 2771 then
0
else
0)
else
(if i.val < 2773 then
0
else
(if i.val < 2774 then
0
else
0)))
else
(if i.val < 2777 then
(if i.val < 2776 then
0
else
0)
else
(if i.val < 2778 then
0
else
(if i.val < 2779 then
0
else
0)))))
else
(if i.val < 2790 then
(if i.val < 2785 then
(if i.val < 2782 then
(if i.val < 2781 then
0
else
0)
else
(if i.val < 2783 then
0
else
(if i.val < 2784 then
0
else
0)))
else
(if i.val < 2787 then
(if i.val < 2786 then
0
else
0)
else
(if i.val < 2788 then
0
else
(if i.val < 2789 then
0
else
0))))
else
(if i.val < 2795 then
(if i.val < 2792 then
(if i.val < 2791 then
0
else
0)
else
(if i.val < 2793 then
0
else
(if i.val < 2794 then
0
else
0)))
else
(if i.val < 2797 then
(if i.val < 2796 then
0
else
0)
else
(if i.val < 2798 then
0
else
(if i.val < 2799 then
0
else
0)))))))
else
(if i.val < 2840 then
(if i.val < 2820 then
(if i.val < 2810 then
(if i.val < 2805 then
(if i.val < 2802 then
(if i.val < 2801 then
0
else
0)
else
(if i.val < 2803 then
0
else
(if i.val < 2804 then
0
else
0)))
else
(if i.val < 2807 then
(if i.val < 2806 then
0
else
0)
else
(if i.val < 2808 then
0
else
(if i.val < 2809 then
0
else
0))))
else
(if i.val < 2815 then
(if i.val < 2812 then
(if i.val < 2811 then
0
else
0)
else
(if i.val < 2813 then
0
else
(if i.val < 2814 then
0
else
0)))
else
(if i.val < 2817 then
(if i.val < 2816 then
0
else
0)
else
(if i.val < 2818 then
0
else
(if i.val < 2819 then
0
else
0)))))
else
(if i.val < 2830 then
(if i.val < 2825 then
(if i.val < 2822 then
(if i.val < 2821 then
0
else
0)
else
(if i.val < 2823 then
0
else
(if i.val < 2824 then
0
else
0)))
else
(if i.val < 2827 then
(if i.val < 2826 then
0
else
0)
else
(if i.val < 2828 then
0
else
(if i.val < 2829 then
0
else
0))))
else
(if i.val < 2835 then
(if i.val < 2832 then
(if i.val < 2831 then
0
else
0)
else
(if i.val < 2833 then
0
else
(if i.val < 2834 then
0
else
0)))
else
(if i.val < 2837 then
(if i.val < 2836 then
0
else
0)
else
(if i.val < 2838 then
0
else
(if i.val < 2839 then
0
else
0))))))
else
(if i.val < 2860 then
(if i.val < 2850 then
(if i.val < 2845 then
(if i.val < 2842 then
(if i.val < 2841 then
0
else
0)
else
(if i.val < 2843 then
0
else
(if i.val < 2844 then
0
else
0)))
else
(if i.val < 2847 then
(if i.val < 2846 then
0
else
0)
else
(if i.val < 2848 then
0
else
(if i.val < 2849 then
0
else
0))))
else
(if i.val < 2855 then
(if i.val < 2852 then
(if i.val < 2851 then
0
else
0)
else
(if i.val < 2853 then
0
else
(if i.val < 2854 then
0
else
0)))
else
(if i.val < 2857 then
(if i.val < 2856 then
0
else
0)
else
(if i.val < 2858 then
0
else
(if i.val < 2859 then
0
else
0)))))
else
(if i.val < 2870 then
(if i.val < 2865 then
(if i.val < 2862 then
(if i.val < 2861 then
0
else
0)
else
(if i.val < 2863 then
0
else
(if i.val < 2864 then
0
else
0)))
else
(if i.val < 2867 then
(if i.val < 2866 then
0
else
0)
else
(if i.val < 2868 then
0
else
(if i.val < 2869 then
0
else
0))))
else
(if i.val < 2875 then
(if i.val < 2872 then
(if i.val < 2871 then
0
else
0)
else
(if i.val < 2873 then
0
else
(if i.val < 2874 then
0
else
0)))
else
(if i.val < 2877 then
(if i.val < 2876 then
0
else
0)
else
(if i.val < 2878 then
0
else
(if i.val < 2879 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetMonodromies1Part0000 : Fin 2880 → Fin 18 :=
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

def g32p_row31_cosetMonodromies1Part0001 : Fin 2880 → Fin 18 :=
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
0)
else
(if i.val < 715 then
0
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
0
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
0
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
0)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
0
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
0
else
0)
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
0)
else
(if i.val < 751 then
0
else
0))))
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
0))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
0)
else
(if i.val < 759 then
0
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
0
else
0)
else
(if i.val < 763 then
0
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
0
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
0
else
0)
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
0
else
0)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
0)
else
(if i.val < 779 then
0
else
0))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
0)
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
0))
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
0
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
0
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
0)
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

def g32p_row31_cosetMonodromies1Part0002 : Fin 2880 → Fin 18 :=
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
0)))
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
0)
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
0)
else
(if i.val < 1155 then
0
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
0)
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
0)
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
0
else
0)
else
(if i.val < 1171 then
0
else
0))
else
(if i.val < 1174 then
(if i.val < 1173 then
0
else
0)
else
(if i.val < 1175 then
0
else
0)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
0
else
0)
else
(if i.val < 1179 then
0
else
0))
else
(if i.val < 1182 then
(if i.val < 1181 then
0
else
0)
else
(if i.val < 1183 then
0
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
0)
else
(if i.val < 1187 then
0
else
0))
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
0
else
0)
else
(if i.val < 1195 then
0
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
0)
else
(if i.val < 1203 then
0
else
0))
else
(if i.val < 1206 then
(if i.val < 1205 then
0
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
0
else
0)
else
(if i.val < 1211 then
0
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
0
else
0))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
0
else
0)
else
(if i.val < 1219 then
0
else
0))
else
(if i.val < 1222 then
(if i.val < 1221 then
0
else
0)
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
0)
else
(if i.val < 1227 then
0
else
0))
else
(if i.val < 1230 then
(if i.val < 1229 then
0
else
0)
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
0)
else
(if i.val < 1255 then
0
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
0
else
0))
else
(if i.val < 1270 then
(if i.val < 1269 then
0
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
0
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
0)
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
0
else
0))
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
0
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
0))
else
(if i.val < 1358 then
(if i.val < 1357 then
0
else
0)
else
(if i.val < 1359 then
0
else
0))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
0
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
0
else
0)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
0
else
0)
else
(if i.val < 1371 then
0
else
0))
else
(if i.val < 1374 then
(if i.val < 1373 then
0
else
0)
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
0
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
0
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
0)
else
(if i.val < 1407 then
0
else
0)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
0
else
0)
else
(if i.val < 1411 then
0
else
0))
else
(if i.val < 1414 then
(if i.val < 1413 then
0
else
0)
else
(if i.val < 1415 then
0
else
0)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
0
else
0)
else
(if i.val < 1419 then
0
else
0))
else
(if i.val < 1422 then
(if i.val < 1421 then
0
else
0)
else
(if i.val < 1423 then
0
else
0))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
0
else
0)
else
(if i.val < 1427 then
0
else
0))
else
(if i.val < 1430 then
(if i.val < 1429 then
0
else
0)
else
(if i.val < 1431 then
0
else
0)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
0
else
0)
else
(if i.val < 1435 then
0
else
0))
else
(if i.val < 1438 then
(if i.val < 1437 then
0
else
0)
else
(if i.val < 1439 then
0
else
0)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
0
else
0)
else
(if i.val < 1443 then
0
else
0))
else
(if i.val < 1446 then
(if i.val < 1445 then
0
else
0)
else
(if i.val < 1447 then
0
else
0)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
0
else
0)
else
(if i.val < 1451 then
0
else
0))
else
(if i.val < 1454 then
(if i.val < 1453 then
0
else
0)
else
(if i.val < 1455 then
0
else
0))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
0
else
0)
else
(if i.val < 1459 then
0
else
0))
else
(if i.val < 1462 then
(if i.val < 1461 then
0
else
0)
else
(if i.val < 1463 then
0
else
0)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
0
else
0)
else
(if i.val < 1467 then
0
else
0))
else
(if i.val < 1470 then
(if i.val < 1469 then
0
else
0)
else
(if i.val < 1471 then
0
else
0))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
0
else
0)
else
(if i.val < 1475 then
0
else
0))
else
(if i.val < 1478 then
(if i.val < 1477 then
0
else
0)
else
(if i.val < 1479 then
0
else
0)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
0
else
0)
else
(if i.val < 1483 then
0
else
0))
else
(if i.val < 1486 then
(if i.val < 1485 then
0
else
0)
else
(if i.val < 1487 then
0
else
0))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
0
else
0)
else
(if i.val < 1491 then
0
else
0))
else
(if i.val < 1494 then
(if i.val < 1493 then
0
else
0)
else
(if i.val < 1495 then
0
else
0)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
0
else
0)
else
(if i.val < 1499 then
0
else
0))
else
(if i.val < 1502 then
(if i.val < 1501 then
0
else
0)
else
(if i.val < 1503 then
0
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
0)
else
(if i.val < 1507 then
0
else
0))
else
(if i.val < 1510 then
(if i.val < 1509 then
0
else
0)
else
(if i.val < 1511 then
0
else
0)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
0
else
0)
else
(if i.val < 1515 then
0
else
0))
else
(if i.val < 1518 then
(if i.val < 1517 then
0
else
0)
else
(if i.val < 1519 then
0
else
0))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
0
else
0)
else
(if i.val < 1523 then
0
else
0))
else
(if i.val < 1526 then
(if i.val < 1525 then
0
else
0)
else
(if i.val < 1527 then
0
else
0)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
0
else
0)
else
(if i.val < 1531 then
0
else
0))
else
(if i.val < 1534 then
(if i.val < 1533 then
0
else
0)
else
(if i.val < 1535 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetMonodromies1Part0003 : Fin 2880 → Fin 18 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
0
else
0)
else
(if i.val < 1539 then
0
else
0))
else
(if i.val < 1542 then
(if i.val < 1541 then
0
else
0)
else
(if i.val < 1543 then
0
else
0)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
0
else
0)
else
(if i.val < 1547 then
0
else
0))
else
(if i.val < 1550 then
(if i.val < 1549 then
0
else
0)
else
(if i.val < 1551 then
0
else
0))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
0
else
0)
else
(if i.val < 1555 then
0
else
0))
else
(if i.val < 1558 then
(if i.val < 1557 then
0
else
0)
else
(if i.val < 1559 then
0
else
0)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
0
else
0)
else
(if i.val < 1563 then
0
else
0))
else
(if i.val < 1566 then
(if i.val < 1565 then
0
else
0)
else
(if i.val < 1567 then
0
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
0)
else
(if i.val < 1571 then
0
else
0))
else
(if i.val < 1574 then
(if i.val < 1573 then
0
else
0)
else
(if i.val < 1575 then
0
else
0)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
0
else
0)
else
(if i.val < 1579 then
0
else
0))
else
(if i.val < 1582 then
(if i.val < 1581 then
0
else
0)
else
(if i.val < 1583 then
0
else
0))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
0
else
0)
else
(if i.val < 1587 then
0
else
0))
else
(if i.val < 1590 then
(if i.val < 1589 then
0
else
0)
else
(if i.val < 1591 then
0
else
0)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
0
else
0)
else
(if i.val < 1595 then
0
else
0))
else
(if i.val < 1598 then
(if i.val < 1597 then
0
else
0)
else
(if i.val < 1599 then
0
else
0))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
0
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
0
else
0)
else
(if i.val < 1607 then
0
else
0)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
0
else
0)
else
(if i.val < 1611 then
0
else
0))
else
(if i.val < 1614 then
(if i.val < 1613 then
0
else
0)
else
(if i.val < 1615 then
0
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
0
else
0))
else
(if i.val < 1622 then
(if i.val < 1621 then
0
else
0)
else
(if i.val < 1623 then
0
else
0)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
0
else
0)
else
(if i.val < 1627 then
0
else
0))
else
(if i.val < 1630 then
(if i.val < 1629 then
0
else
0)
else
(if i.val < 1631 then
0
else
0)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
0
else
0)
else
(if i.val < 1635 then
0
else
0))
else
(if i.val < 1638 then
(if i.val < 1637 then
0
else
0)
else
(if i.val < 1639 then
0
else
0)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
0
else
0)
else
(if i.val < 1643 then
0
else
0))
else
(if i.val < 1646 then
(if i.val < 1645 then
0
else
0)
else
(if i.val < 1647 then
0
else
0))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
0
else
0)
else
(if i.val < 1651 then
0
else
0))
else
(if i.val < 1654 then
(if i.val < 1653 then
0
else
0)
else
(if i.val < 1655 then
0
else
0)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
0
else
0)
else
(if i.val < 1659 then
0
else
0))
else
(if i.val < 1662 then
(if i.val < 1661 then
0
else
0)
else
(if i.val < 1663 then
0
else
0)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
0
else
0)
else
(if i.val < 1667 then
0
else
0))
else
(if i.val < 1670 then
(if i.val < 1669 then
0
else
0)
else
(if i.val < 1671 then
0
else
0)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
0
else
0)
else
(if i.val < 1675 then
0
else
0))
else
(if i.val < 1678 then
(if i.val < 1677 then
0
else
0)
else
(if i.val < 1679 then
0
else
0))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
0
else
0)
else
(if i.val < 1683 then
0
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
0
else
0)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
0
else
0)
else
(if i.val < 1691 then
0
else
0))
else
(if i.val < 1694 then
(if i.val < 1693 then
0
else
0)
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
0)
else
(if i.val < 1699 then
0
else
0))
else
(if i.val < 1702 then
(if i.val < 1701 then
0
else
0)
else
(if i.val < 1703 then
0
else
0)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
0
else
0)
else
(if i.val < 1707 then
0
else
0))
else
(if i.val < 1710 then
(if i.val < 1709 then
0
else
0)
else
(if i.val < 1711 then
0
else
0))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
0
else
0)
else
(if i.val < 1715 then
0
else
0))
else
(if i.val < 1718 then
(if i.val < 1717 then
0
else
0)
else
(if i.val < 1719 then
0
else
0)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
0
else
0)
else
(if i.val < 1723 then
0
else
0))
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
0
else
0)
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
0)
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
0)
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
0)))))
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
0)
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
0)))
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
0))
else
(if i.val < 1822 then
(if i.val < 1821 then
0
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
0
else
0)
else
(if i.val < 1827 then
0
else
0))
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
0
else
0)
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
0
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
0)
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
0
else
0))
else
(if i.val < 1854 then
(if i.val < 1853 then
0
else
0)
else
(if i.val < 1855 then
0
else
0))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
0
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
0)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
0
else
0)
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
0)
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
0))
else
(if i.val < 1878 then
(if i.val < 1877 then
0
else
0)
else
(if i.val < 1879 then
0
else
0)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
0
else
0)
else
(if i.val < 1883 then
0
else
0))
else
(if i.val < 1886 then
(if i.val < 1885 then
0
else
0)
else
(if i.val < 1887 then
0
else
0)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
0
else
0)
else
(if i.val < 1891 then
0
else
0))
else
(if i.val < 1894 then
(if i.val < 1893 then
0
else
0)
else
(if i.val < 1895 then
0
else
0)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
0
else
0)
else
(if i.val < 1899 then
0
else
0))
else
(if i.val < 1902 then
(if i.val < 1901 then
0
else
0)
else
(if i.val < 1903 then
0
else
0))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
0
else
0)
else
(if i.val < 1907 then
0
else
0))
else
(if i.val < 1910 then
(if i.val < 1909 then
0
else
0)
else
(if i.val < 1911 then
0
else
0)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
0
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
0
else
0)
else
(if i.val < 1919 then
0
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
0
else
0)
else
(if i.val < 1923 then
0
else
0))
else
(if i.val < 1926 then
(if i.val < 1925 then
0
else
0)
else
(if i.val < 1927 then
0
else
0)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
0
else
0)
else
(if i.val < 1931 then
0
else
0))
else
(if i.val < 1934 then
(if i.val < 1933 then
0
else
0)
else
(if i.val < 1935 then
0
else
0))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
0
else
0)
else
(if i.val < 1939 then
0
else
0))
else
(if i.val < 1942 then
(if i.val < 1941 then
0
else
0)
else
(if i.val < 1943 then
0
else
0)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
0
else
0)
else
(if i.val < 1947 then
0
else
0))
else
(if i.val < 1950 then
(if i.val < 1949 then
0
else
0)
else
(if i.val < 1951 then
0
else
0)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
0
else
0)
else
(if i.val < 1955 then
0
else
0))
else
(if i.val < 1958 then
(if i.val < 1957 then
0
else
0)
else
(if i.val < 1959 then
0
else
0)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
0
else
0)
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
0)
else
(if i.val < 1967 then
0
else
0))))
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
0
else
0))
else
(if i.val < 1974 then
(if i.val < 1973 then
0
else
0)
else
(if i.val < 1975 then
0
else
0)))
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
0))
else
(if i.val < 1982 then
(if i.val < 1981 then
0
else
0)
else
(if i.val < 1983 then
0
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
0)
else
(if i.val < 1987 then
0
else
0))
else
(if i.val < 1990 then
(if i.val < 1989 then
0
else
0)
else
(if i.val < 1991 then
0
else
0)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
0
else
0)
else
(if i.val < 1995 then
0
else
0))
else
(if i.val < 1998 then
(if i.val < 1997 then
0
else
0)
else
(if i.val < 1999 then
0
else
0))))
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

def g32p_row31_cosetMonodromies1Part0004 : Fin 2880 → Fin 18 :=
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
0)
else
(if i.val < 2303 then
0
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
0
else
0)
else
(if i.val < 2307 then
0
else
0))
else
(if i.val < 2310 then
(if i.val < 2309 then
0
else
0)
else
(if i.val < 2311 then
0
else
0)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
0
else
0)
else
(if i.val < 2315 then
0
else
0))
else
(if i.val < 2318 then
(if i.val < 2317 then
0
else
0)
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
0
else
0)
else
(if i.val < 2323 then
0
else
0))
else
(if i.val < 2326 then
(if i.val < 2325 then
0
else
0)
else
(if i.val < 2327 then
0
else
0)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
0
else
0)
else
(if i.val < 2331 then
0
else
0))
else
(if i.val < 2334 then
(if i.val < 2333 then
0
else
0)
else
(if i.val < 2335 then
0
else
0)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
0
else
0)
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
0
else
0)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
0
else
0)
else
(if i.val < 2347 then
0
else
0))
else
(if i.val < 2350 then
(if i.val < 2349 then
0
else
0)
else
(if i.val < 2351 then
0
else
0))))
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
0)
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
0)
else
(if i.val < 2363 then
0
else
0))
else
(if i.val < 2366 then
(if i.val < 2365 then
0
else
0)
else
(if i.val < 2367 then
0
else
0))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
0
else
0)
else
(if i.val < 2371 then
0
else
0))
else
(if i.val < 2374 then
(if i.val < 2373 then
0
else
0)
else
(if i.val < 2375 then
0
else
0)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
0
else
0)
else
(if i.val < 2379 then
0
else
0))
else
(if i.val < 2382 then
(if i.val < 2381 then
0
else
0)
else
(if i.val < 2383 then
0
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
0))
else
(if i.val < 2406 then
(if i.val < 2405 then
0
else
0)
else
(if i.val < 2407 then
0
else
0)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
0
else
0)
else
(if i.val < 2411 then
0
else
0))
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
0))))
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
0
else
0))
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
0)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
0
else
0)
else
(if i.val < 2427 then
0
else
0))
else
(if i.val < 2430 then
(if i.val < 2429 then
0
else
0)
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
0
else
0)
else
(if i.val < 2435 then
0
else
0))
else
(if i.val < 2438 then
(if i.val < 2437 then
0
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
0
else
0)
else
(if i.val < 2443 then
0
else
0))
else
(if i.val < 2446 then
(if i.val < 2445 then
0
else
0)
else
(if i.val < 2447 then
0
else
0))))
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
0
else
0))
else
(if i.val < 2454 then
(if i.val < 2453 then
0
else
0)
else
(if i.val < 2455 then
0
else
0)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
0
else
0)
else
(if i.val < 2459 then
0
else
0))
else
(if i.val < 2462 then
(if i.val < 2461 then
0
else
0)
else
(if i.val < 2463 then
0
else
0)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
0
else
0)
else
(if i.val < 2467 then
0
else
0))
else
(if i.val < 2470 then
(if i.val < 2469 then
0
else
0)
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
0
else
0))
else
(if i.val < 2478 then
(if i.val < 2477 then
0
else
0)
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
0
else
0)
else
(if i.val < 2483 then
0
else
0))
else
(if i.val < 2486 then
(if i.val < 2485 then
0
else
0)
else
(if i.val < 2487 then
0
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
0
else
0))
else
(if i.val < 2494 then
(if i.val < 2493 then
0
else
0)
else
(if i.val < 2495 then
0
else
0))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
0
else
0)
else
(if i.val < 2499 then
0
else
0))
else
(if i.val < 2502 then
(if i.val < 2501 then
0
else
0)
else
(if i.val < 2503 then
0
else
0)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
0
else
0)
else
(if i.val < 2507 then
0
else
0))
else
(if i.val < 2510 then
(if i.val < 2509 then
0
else
0)
else
(if i.val < 2511 then
0
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
0
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
0)
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
0)
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

def g32p_row31_cosetMonodromies1Part0005 : Fin 2880 → Fin 18 :=
  fun i => (if i.val < 2720 then
(if i.val < 2640 then
(if i.val < 2600 then
(if i.val < 2580 then
(if i.val < 2570 then
(if i.val < 2565 then
(if i.val < 2562 then
(if i.val < 2561 then
0
else
0)
else
(if i.val < 2563 then
0
else
(if i.val < 2564 then
0
else
0)))
else
(if i.val < 2567 then
(if i.val < 2566 then
0
else
0)
else
(if i.val < 2568 then
0
else
(if i.val < 2569 then
0
else
0))))
else
(if i.val < 2575 then
(if i.val < 2572 then
(if i.val < 2571 then
0
else
0)
else
(if i.val < 2573 then
0
else
(if i.val < 2574 then
0
else
0)))
else
(if i.val < 2577 then
(if i.val < 2576 then
0
else
0)
else
(if i.val < 2578 then
0
else
(if i.val < 2579 then
0
else
0)))))
else
(if i.val < 2590 then
(if i.val < 2585 then
(if i.val < 2582 then
(if i.val < 2581 then
0
else
0)
else
(if i.val < 2583 then
0
else
(if i.val < 2584 then
0
else
0)))
else
(if i.val < 2587 then
(if i.val < 2586 then
0
else
0)
else
(if i.val < 2588 then
0
else
(if i.val < 2589 then
0
else
0))))
else
(if i.val < 2595 then
(if i.val < 2592 then
(if i.val < 2591 then
0
else
0)
else
(if i.val < 2593 then
0
else
(if i.val < 2594 then
0
else
0)))
else
(if i.val < 2597 then
(if i.val < 2596 then
0
else
0)
else
(if i.val < 2598 then
0
else
(if i.val < 2599 then
0
else
0))))))
else
(if i.val < 2620 then
(if i.val < 2610 then
(if i.val < 2605 then
(if i.val < 2602 then
(if i.val < 2601 then
0
else
0)
else
(if i.val < 2603 then
0
else
(if i.val < 2604 then
0
else
0)))
else
(if i.val < 2607 then
(if i.val < 2606 then
0
else
0)
else
(if i.val < 2608 then
0
else
(if i.val < 2609 then
0
else
0))))
else
(if i.val < 2615 then
(if i.val < 2612 then
(if i.val < 2611 then
0
else
0)
else
(if i.val < 2613 then
0
else
(if i.val < 2614 then
0
else
0)))
else
(if i.val < 2617 then
(if i.val < 2616 then
0
else
0)
else
(if i.val < 2618 then
0
else
(if i.val < 2619 then
0
else
0)))))
else
(if i.val < 2630 then
(if i.val < 2625 then
(if i.val < 2622 then
(if i.val < 2621 then
0
else
0)
else
(if i.val < 2623 then
0
else
(if i.val < 2624 then
0
else
0)))
else
(if i.val < 2627 then
(if i.val < 2626 then
0
else
0)
else
(if i.val < 2628 then
0
else
(if i.val < 2629 then
0
else
0))))
else
(if i.val < 2635 then
(if i.val < 2632 then
(if i.val < 2631 then
0
else
0)
else
(if i.val < 2633 then
0
else
(if i.val < 2634 then
0
else
0)))
else
(if i.val < 2637 then
(if i.val < 2636 then
0
else
0)
else
(if i.val < 2638 then
0
else
(if i.val < 2639 then
0
else
0)))))))
else
(if i.val < 2680 then
(if i.val < 2660 then
(if i.val < 2650 then
(if i.val < 2645 then
(if i.val < 2642 then
(if i.val < 2641 then
0
else
0)
else
(if i.val < 2643 then
0
else
(if i.val < 2644 then
0
else
0)))
else
(if i.val < 2647 then
(if i.val < 2646 then
0
else
0)
else
(if i.val < 2648 then
0
else
(if i.val < 2649 then
0
else
0))))
else
(if i.val < 2655 then
(if i.val < 2652 then
(if i.val < 2651 then
0
else
0)
else
(if i.val < 2653 then
0
else
(if i.val < 2654 then
0
else
0)))
else
(if i.val < 2657 then
(if i.val < 2656 then
0
else
0)
else
(if i.val < 2658 then
0
else
(if i.val < 2659 then
0
else
0)))))
else
(if i.val < 2670 then
(if i.val < 2665 then
(if i.val < 2662 then
(if i.val < 2661 then
0
else
0)
else
(if i.val < 2663 then
0
else
(if i.val < 2664 then
0
else
0)))
else
(if i.val < 2667 then
(if i.val < 2666 then
0
else
0)
else
(if i.val < 2668 then
0
else
(if i.val < 2669 then
0
else
0))))
else
(if i.val < 2675 then
(if i.val < 2672 then
(if i.val < 2671 then
0
else
0)
else
(if i.val < 2673 then
0
else
(if i.val < 2674 then
0
else
0)))
else
(if i.val < 2677 then
(if i.val < 2676 then
0
else
0)
else
(if i.val < 2678 then
0
else
(if i.val < 2679 then
0
else
0))))))
else
(if i.val < 2700 then
(if i.val < 2690 then
(if i.val < 2685 then
(if i.val < 2682 then
(if i.val < 2681 then
0
else
0)
else
(if i.val < 2683 then
0
else
(if i.val < 2684 then
0
else
0)))
else
(if i.val < 2687 then
(if i.val < 2686 then
0
else
0)
else
(if i.val < 2688 then
0
else
(if i.val < 2689 then
0
else
0))))
else
(if i.val < 2695 then
(if i.val < 2692 then
(if i.val < 2691 then
0
else
0)
else
(if i.val < 2693 then
0
else
(if i.val < 2694 then
0
else
0)))
else
(if i.val < 2697 then
(if i.val < 2696 then
0
else
0)
else
(if i.val < 2698 then
0
else
(if i.val < 2699 then
0
else
0)))))
else
(if i.val < 2710 then
(if i.val < 2705 then
(if i.val < 2702 then
(if i.val < 2701 then
0
else
0)
else
(if i.val < 2703 then
0
else
(if i.val < 2704 then
0
else
0)))
else
(if i.val < 2707 then
(if i.val < 2706 then
0
else
0)
else
(if i.val < 2708 then
0
else
(if i.val < 2709 then
0
else
0))))
else
(if i.val < 2715 then
(if i.val < 2712 then
(if i.val < 2711 then
0
else
0)
else
(if i.val < 2713 then
0
else
(if i.val < 2714 then
0
else
0)))
else
(if i.val < 2717 then
(if i.val < 2716 then
0
else
0)
else
(if i.val < 2718 then
0
else
(if i.val < 2719 then
0
else
0))))))))
else
(if i.val < 2800 then
(if i.val < 2760 then
(if i.val < 2740 then
(if i.val < 2730 then
(if i.val < 2725 then
(if i.val < 2722 then
(if i.val < 2721 then
0
else
0)
else
(if i.val < 2723 then
0
else
(if i.val < 2724 then
0
else
0)))
else
(if i.val < 2727 then
(if i.val < 2726 then
0
else
0)
else
(if i.val < 2728 then
0
else
(if i.val < 2729 then
0
else
0))))
else
(if i.val < 2735 then
(if i.val < 2732 then
(if i.val < 2731 then
0
else
0)
else
(if i.val < 2733 then
0
else
(if i.val < 2734 then
0
else
0)))
else
(if i.val < 2737 then
(if i.val < 2736 then
0
else
0)
else
(if i.val < 2738 then
0
else
(if i.val < 2739 then
0
else
0)))))
else
(if i.val < 2750 then
(if i.val < 2745 then
(if i.val < 2742 then
(if i.val < 2741 then
0
else
0)
else
(if i.val < 2743 then
0
else
(if i.val < 2744 then
0
else
0)))
else
(if i.val < 2747 then
(if i.val < 2746 then
0
else
0)
else
(if i.val < 2748 then
0
else
(if i.val < 2749 then
0
else
0))))
else
(if i.val < 2755 then
(if i.val < 2752 then
(if i.val < 2751 then
0
else
0)
else
(if i.val < 2753 then
0
else
(if i.val < 2754 then
0
else
0)))
else
(if i.val < 2757 then
(if i.val < 2756 then
0
else
0)
else
(if i.val < 2758 then
0
else
(if i.val < 2759 then
0
else
0))))))
else
(if i.val < 2780 then
(if i.val < 2770 then
(if i.val < 2765 then
(if i.val < 2762 then
(if i.val < 2761 then
0
else
0)
else
(if i.val < 2763 then
0
else
(if i.val < 2764 then
0
else
0)))
else
(if i.val < 2767 then
(if i.val < 2766 then
0
else
0)
else
(if i.val < 2768 then
0
else
(if i.val < 2769 then
0
else
0))))
else
(if i.val < 2775 then
(if i.val < 2772 then
(if i.val < 2771 then
0
else
0)
else
(if i.val < 2773 then
0
else
(if i.val < 2774 then
0
else
0)))
else
(if i.val < 2777 then
(if i.val < 2776 then
0
else
0)
else
(if i.val < 2778 then
0
else
(if i.val < 2779 then
0
else
0)))))
else
(if i.val < 2790 then
(if i.val < 2785 then
(if i.val < 2782 then
(if i.val < 2781 then
0
else
0)
else
(if i.val < 2783 then
0
else
(if i.val < 2784 then
0
else
0)))
else
(if i.val < 2787 then
(if i.val < 2786 then
0
else
0)
else
(if i.val < 2788 then
0
else
(if i.val < 2789 then
0
else
0))))
else
(if i.val < 2795 then
(if i.val < 2792 then
(if i.val < 2791 then
0
else
0)
else
(if i.val < 2793 then
0
else
(if i.val < 2794 then
0
else
0)))
else
(if i.val < 2797 then
(if i.val < 2796 then
0
else
0)
else
(if i.val < 2798 then
0
else
(if i.val < 2799 then
0
else
0)))))))
else
(if i.val < 2840 then
(if i.val < 2820 then
(if i.val < 2810 then
(if i.val < 2805 then
(if i.val < 2802 then
(if i.val < 2801 then
0
else
0)
else
(if i.val < 2803 then
0
else
(if i.val < 2804 then
0
else
0)))
else
(if i.val < 2807 then
(if i.val < 2806 then
0
else
0)
else
(if i.val < 2808 then
0
else
(if i.val < 2809 then
0
else
0))))
else
(if i.val < 2815 then
(if i.val < 2812 then
(if i.val < 2811 then
0
else
0)
else
(if i.val < 2813 then
0
else
(if i.val < 2814 then
0
else
0)))
else
(if i.val < 2817 then
(if i.val < 2816 then
0
else
0)
else
(if i.val < 2818 then
0
else
(if i.val < 2819 then
0
else
0)))))
else
(if i.val < 2830 then
(if i.val < 2825 then
(if i.val < 2822 then
(if i.val < 2821 then
0
else
0)
else
(if i.val < 2823 then
0
else
(if i.val < 2824 then
0
else
0)))
else
(if i.val < 2827 then
(if i.val < 2826 then
0
else
0)
else
(if i.val < 2828 then
0
else
(if i.val < 2829 then
0
else
0))))
else
(if i.val < 2835 then
(if i.val < 2832 then
(if i.val < 2831 then
0
else
0)
else
(if i.val < 2833 then
0
else
(if i.val < 2834 then
0
else
0)))
else
(if i.val < 2837 then
(if i.val < 2836 then
0
else
0)
else
(if i.val < 2838 then
0
else
(if i.val < 2839 then
0
else
0))))))
else
(if i.val < 2860 then
(if i.val < 2850 then
(if i.val < 2845 then
(if i.val < 2842 then
(if i.val < 2841 then
0
else
0)
else
(if i.val < 2843 then
0
else
(if i.val < 2844 then
0
else
0)))
else
(if i.val < 2847 then
(if i.val < 2846 then
0
else
0)
else
(if i.val < 2848 then
0
else
(if i.val < 2849 then
0
else
0))))
else
(if i.val < 2855 then
(if i.val < 2852 then
(if i.val < 2851 then
0
else
0)
else
(if i.val < 2853 then
0
else
(if i.val < 2854 then
0
else
0)))
else
(if i.val < 2857 then
(if i.val < 2856 then
0
else
0)
else
(if i.val < 2858 then
0
else
(if i.val < 2859 then
0
else
0)))))
else
(if i.val < 2870 then
(if i.val < 2865 then
(if i.val < 2862 then
(if i.val < 2861 then
0
else
0)
else
(if i.val < 2863 then
0
else
(if i.val < 2864 then
0
else
0)))
else
(if i.val < 2867 then
(if i.val < 2866 then
0
else
0)
else
(if i.val < 2868 then
0
else
(if i.val < 2869 then
0
else
0))))
else
(if i.val < 2875 then
(if i.val < 2872 then
(if i.val < 2871 then
0
else
0)
else
(if i.val < 2873 then
0
else
(if i.val < 2874 then
0
else
0)))
else
(if i.val < 2877 then
(if i.val < 2876 then
0
else
0)
else
(if i.val < 2878 then
0
else
(if i.val < 2879 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetMonodromies2Part0000 : Fin 4368 → Fin 18 :=
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
6)
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
6))
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
6)
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
6)
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
6
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

def g32p_row31_cosetMonodromies2Part0001 : Fin 4368 → Fin 18 :=
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
0)
else
(if i.val < 715 then
0
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
0
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
0
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
0)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
0
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
0
else
0)
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
0)
else
(if i.val < 751 then
0
else
0))))
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
0))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
0)
else
(if i.val < 759 then
0
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
0
else
0)
else
(if i.val < 763 then
0
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
0
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
0
else
0)
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
0
else
0)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
0)
else
(if i.val < 779 then
0
else
0))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
0)
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
0))
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
0
else
6))
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
0
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
0)
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

def g32p_row31_cosetMonodromies2Part0002 : Fin 4368 → Fin 18 :=
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
6))
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
6)
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
0)))
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
0)
else
(if i.val < 1151 then
6
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
0)
else
(if i.val < 1155 then
0
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
0)
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
0)
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
0
else
0)
else
(if i.val < 1171 then
0
else
0))
else
(if i.val < 1174 then
(if i.val < 1173 then
0
else
0)
else
(if i.val < 1175 then
0
else
0)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
0
else
0)
else
(if i.val < 1179 then
0
else
6))
else
(if i.val < 1182 then
(if i.val < 1181 then
0
else
0)
else
(if i.val < 1183 then
0
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
0)
else
(if i.val < 1187 then
0
else
0))
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
0
else
0)
else
(if i.val < 1195 then
0
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
0)
else
(if i.val < 1203 then
0
else
0))
else
(if i.val < 1206 then
(if i.val < 1205 then
0
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
0
else
0)
else
(if i.val < 1211 then
0
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
0
else
0))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
0
else
0)
else
(if i.val < 1219 then
0
else
0))
else
(if i.val < 1222 then
(if i.val < 1221 then
0
else
0)
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
0)
else
(if i.val < 1227 then
0
else
0))
else
(if i.val < 1230 then
(if i.val < 1229 then
0
else
0)
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
0)
else
(if i.val < 1255 then
0
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
0
else
0))
else
(if i.val < 1270 then
(if i.val < 1269 then
0
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
0
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
0)
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
0
else
0))
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
0
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
0))
else
(if i.val < 1358 then
(if i.val < 1357 then
0
else
0)
else
(if i.val < 1359 then
0
else
0))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
0
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
0
else
0)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
0
else
0)
else
(if i.val < 1371 then
0
else
0))
else
(if i.val < 1374 then
(if i.val < 1373 then
0
else
0)
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
6)
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
0
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
0
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
0)
else
(if i.val < 1407 then
0
else
0)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
0
else
0)
else
(if i.val < 1411 then
0
else
0))
else
(if i.val < 1414 then
(if i.val < 1413 then
0
else
0)
else
(if i.val < 1415 then
0
else
0)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
0
else
0)
else
(if i.val < 1419 then
0
else
0))
else
(if i.val < 1422 then
(if i.val < 1421 then
0
else
0)
else
(if i.val < 1423 then
0
else
0))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
0
else
0)
else
(if i.val < 1427 then
0
else
0))
else
(if i.val < 1430 then
(if i.val < 1429 then
0
else
0)
else
(if i.val < 1431 then
0
else
0)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
0
else
0)
else
(if i.val < 1435 then
0
else
0))
else
(if i.val < 1438 then
(if i.val < 1437 then
0
else
0)
else
(if i.val < 1439 then
0
else
0)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
0
else
0)
else
(if i.val < 1443 then
0
else
0))
else
(if i.val < 1446 then
(if i.val < 1445 then
0
else
0)
else
(if i.val < 1447 then
0
else
0)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
0
else
0)
else
(if i.val < 1451 then
0
else
0))
else
(if i.val < 1454 then
(if i.val < 1453 then
0
else
0)
else
(if i.val < 1455 then
0
else
0))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
0
else
0)
else
(if i.val < 1459 then
0
else
0))
else
(if i.val < 1462 then
(if i.val < 1461 then
0
else
0)
else
(if i.val < 1463 then
0
else
0)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
0
else
0)
else
(if i.val < 1467 then
0
else
0))
else
(if i.val < 1470 then
(if i.val < 1469 then
0
else
0)
else
(if i.val < 1471 then
0
else
0))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
0
else
0)
else
(if i.val < 1475 then
0
else
0))
else
(if i.val < 1478 then
(if i.val < 1477 then
0
else
0)
else
(if i.val < 1479 then
0
else
0)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
0
else
0)
else
(if i.val < 1483 then
0
else
0))
else
(if i.val < 1486 then
(if i.val < 1485 then
0
else
0)
else
(if i.val < 1487 then
0
else
0))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
0
else
0)
else
(if i.val < 1491 then
0
else
0))
else
(if i.val < 1494 then
(if i.val < 1493 then
0
else
0)
else
(if i.val < 1495 then
0
else
0)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
0
else
0)
else
(if i.val < 1499 then
0
else
0))
else
(if i.val < 1502 then
(if i.val < 1501 then
0
else
0)
else
(if i.val < 1503 then
0
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
0)
else
(if i.val < 1507 then
0
else
0))
else
(if i.val < 1510 then
(if i.val < 1509 then
0
else
0)
else
(if i.val < 1511 then
0
else
0)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
0
else
0)
else
(if i.val < 1515 then
0
else
0))
else
(if i.val < 1518 then
(if i.val < 1517 then
0
else
0)
else
(if i.val < 1519 then
0
else
0))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
0
else
0)
else
(if i.val < 1523 then
0
else
0))
else
(if i.val < 1526 then
(if i.val < 1525 then
0
else
0)
else
(if i.val < 1527 then
0
else
0)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
0
else
0)
else
(if i.val < 1531 then
0
else
0))
else
(if i.val < 1534 then
(if i.val < 1533 then
0
else
0)
else
(if i.val < 1535 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetMonodromies2Part0003 : Fin 4368 → Fin 18 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
0
else
0)
else
(if i.val < 1539 then
0
else
0))
else
(if i.val < 1542 then
(if i.val < 1541 then
0
else
0)
else
(if i.val < 1543 then
0
else
6)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
0
else
0)
else
(if i.val < 1547 then
0
else
0))
else
(if i.val < 1550 then
(if i.val < 1549 then
0
else
0)
else
(if i.val < 1551 then
0
else
0))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
0
else
0)
else
(if i.val < 1555 then
0
else
0))
else
(if i.val < 1558 then
(if i.val < 1557 then
0
else
0)
else
(if i.val < 1559 then
0
else
0)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
0
else
0)
else
(if i.val < 1563 then
0
else
0))
else
(if i.val < 1566 then
(if i.val < 1565 then
0
else
0)
else
(if i.val < 1567 then
0
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
0)
else
(if i.val < 1571 then
0
else
0))
else
(if i.val < 1574 then
(if i.val < 1573 then
0
else
0)
else
(if i.val < 1575 then
0
else
0)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
0
else
0)
else
(if i.val < 1579 then
0
else
0))
else
(if i.val < 1582 then
(if i.val < 1581 then
0
else
0)
else
(if i.val < 1583 then
0
else
0))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
0
else
0)
else
(if i.val < 1587 then
0
else
0))
else
(if i.val < 1590 then
(if i.val < 1589 then
0
else
0)
else
(if i.val < 1591 then
0
else
0)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
0
else
0)
else
(if i.val < 1595 then
0
else
0))
else
(if i.val < 1598 then
(if i.val < 1597 then
0
else
0)
else
(if i.val < 1599 then
0
else
0))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
0
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
0
else
0)
else
(if i.val < 1607 then
0
else
0)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
0
else
0)
else
(if i.val < 1611 then
0
else
0))
else
(if i.val < 1614 then
(if i.val < 1613 then
0
else
0)
else
(if i.val < 1615 then
0
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
0
else
0))
else
(if i.val < 1622 then
(if i.val < 1621 then
0
else
0)
else
(if i.val < 1623 then
0
else
0)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
0
else
0)
else
(if i.val < 1627 then
0
else
0))
else
(if i.val < 1630 then
(if i.val < 1629 then
0
else
0)
else
(if i.val < 1631 then
0
else
0)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
0
else
0)
else
(if i.val < 1635 then
0
else
0))
else
(if i.val < 1638 then
(if i.val < 1637 then
0
else
0)
else
(if i.val < 1639 then
0
else
0)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
0
else
0)
else
(if i.val < 1643 then
0
else
0))
else
(if i.val < 1646 then
(if i.val < 1645 then
0
else
0)
else
(if i.val < 1647 then
0
else
0))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
0
else
0)
else
(if i.val < 1651 then
0
else
0))
else
(if i.val < 1654 then
(if i.val < 1653 then
0
else
0)
else
(if i.val < 1655 then
0
else
0)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
0
else
0)
else
(if i.val < 1659 then
0
else
0))
else
(if i.val < 1662 then
(if i.val < 1661 then
0
else
0)
else
(if i.val < 1663 then
0
else
0)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
0
else
0)
else
(if i.val < 1667 then
0
else
0))
else
(if i.val < 1670 then
(if i.val < 1669 then
0
else
0)
else
(if i.val < 1671 then
0
else
0)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
0
else
0)
else
(if i.val < 1675 then
0
else
0))
else
(if i.val < 1678 then
(if i.val < 1677 then
0
else
0)
else
(if i.val < 1679 then
0
else
0))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
0
else
0)
else
(if i.val < 1683 then
0
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
0
else
0)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
0
else
0)
else
(if i.val < 1691 then
0
else
0))
else
(if i.val < 1694 then
(if i.val < 1693 then
0
else
0)
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
0)
else
(if i.val < 1699 then
0
else
0))
else
(if i.val < 1702 then
(if i.val < 1701 then
0
else
0)
else
(if i.val < 1703 then
0
else
0)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
0
else
0)
else
(if i.val < 1707 then
0
else
0))
else
(if i.val < 1710 then
(if i.val < 1709 then
0
else
0)
else
(if i.val < 1711 then
0
else
0))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
0
else
0)
else
(if i.val < 1715 then
0
else
0))
else
(if i.val < 1718 then
(if i.val < 1717 then
0
else
0)
else
(if i.val < 1719 then
0
else
0)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
0
else
0)
else
(if i.val < 1723 then
0
else
0))
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
0
else
0)
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
0)
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
0)
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
0)))))
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
0)
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
0)))
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
0))
else
(if i.val < 1822 then
(if i.val < 1821 then
0
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
0
else
0)
else
(if i.val < 1827 then
0
else
0))
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
0
else
0)
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
0
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
0)
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
0
else
0))
else
(if i.val < 1854 then
(if i.val < 1853 then
0
else
0)
else
(if i.val < 1855 then
0
else
0))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
0
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
0)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
6
else
0)
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
0)
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
0))
else
(if i.val < 1878 then
(if i.val < 1877 then
0
else
0)
else
(if i.val < 1879 then
0
else
0)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
0
else
0)
else
(if i.val < 1883 then
0
else
0))
else
(if i.val < 1886 then
(if i.val < 1885 then
0
else
0)
else
(if i.val < 1887 then
0
else
0)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
0
else
0)
else
(if i.val < 1891 then
0
else
0))
else
(if i.val < 1894 then
(if i.val < 1893 then
0
else
0)
else
(if i.val < 1895 then
0
else
0)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
0
else
0)
else
(if i.val < 1899 then
0
else
0))
else
(if i.val < 1902 then
(if i.val < 1901 then
0
else
0)
else
(if i.val < 1903 then
0
else
0))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
0
else
0)
else
(if i.val < 1907 then
0
else
0))
else
(if i.val < 1910 then
(if i.val < 1909 then
0
else
0)
else
(if i.val < 1911 then
0
else
0)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
0
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
0
else
0)
else
(if i.val < 1919 then
0
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
0
else
0)
else
(if i.val < 1923 then
0
else
0))
else
(if i.val < 1926 then
(if i.val < 1925 then
0
else
0)
else
(if i.val < 1927 then
0
else
0)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
0
else
0)
else
(if i.val < 1931 then
0
else
0))
else
(if i.val < 1934 then
(if i.val < 1933 then
0
else
0)
else
(if i.val < 1935 then
0
else
0))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
0
else
0)
else
(if i.val < 1939 then
0
else
0))
else
(if i.val < 1942 then
(if i.val < 1941 then
0
else
0)
else
(if i.val < 1943 then
0
else
6)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
0
else
0)
else
(if i.val < 1947 then
0
else
0))
else
(if i.val < 1950 then
(if i.val < 1949 then
0
else
0)
else
(if i.val < 1951 then
0
else
0)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
0
else
0)
else
(if i.val < 1955 then
0
else
6))
else
(if i.val < 1958 then
(if i.val < 1957 then
0
else
0)
else
(if i.val < 1959 then
0
else
0)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
0
else
0)
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
0)
else
(if i.val < 1967 then
0
else
0))))
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
0
else
0))
else
(if i.val < 1974 then
(if i.val < 1973 then
0
else
6)
else
(if i.val < 1975 then
0
else
0)))
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
0))
else
(if i.val < 1982 then
(if i.val < 1981 then
0
else
0)
else
(if i.val < 1983 then
0
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
0)
else
(if i.val < 1987 then
0
else
0))
else
(if i.val < 1990 then
(if i.val < 1989 then
0
else
0)
else
(if i.val < 1991 then
0
else
0)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
0
else
0)
else
(if i.val < 1995 then
0
else
0))
else
(if i.val < 1998 then
(if i.val < 1997 then
0
else
0)
else
(if i.val < 1999 then
0
else
0))))
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

def g32p_row31_cosetMonodromies2Part0004 : Fin 4368 → Fin 18 :=
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
6)
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
6
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
6)))))))
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
6
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
6))
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
6)))
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
6
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
0)
else
(if i.val < 2303 then
0
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
0
else
0)
else
(if i.val < 2307 then
0
else
0))
else
(if i.val < 2310 then
(if i.val < 2309 then
0
else
0)
else
(if i.val < 2311 then
0
else
0)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
0
else
0)
else
(if i.val < 2315 then
0
else
0))
else
(if i.val < 2318 then
(if i.val < 2317 then
0
else
0)
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
0
else
0)
else
(if i.val < 2323 then
0
else
0))
else
(if i.val < 2326 then
(if i.val < 2325 then
0
else
0)
else
(if i.val < 2327 then
0
else
0)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
0
else
6)
else
(if i.val < 2331 then
0
else
0))
else
(if i.val < 2334 then
(if i.val < 2333 then
0
else
0)
else
(if i.val < 2335 then
0
else
0)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
0
else
0)
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
0
else
0)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
0
else
0)
else
(if i.val < 2347 then
0
else
0))
else
(if i.val < 2350 then
(if i.val < 2349 then
0
else
0)
else
(if i.val < 2351 then
0
else
0))))
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
0)
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
0)
else
(if i.val < 2363 then
0
else
0))
else
(if i.val < 2366 then
(if i.val < 2365 then
0
else
0)
else
(if i.val < 2367 then
0
else
0))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
0
else
0)
else
(if i.val < 2371 then
0
else
0))
else
(if i.val < 2374 then
(if i.val < 2373 then
0
else
0)
else
(if i.val < 2375 then
0
else
0)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
0
else
0)
else
(if i.val < 2379 then
0
else
0))
else
(if i.val < 2382 then
(if i.val < 2381 then
0
else
0)
else
(if i.val < 2383 then
0
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
0))
else
(if i.val < 2406 then
(if i.val < 2405 then
0
else
0)
else
(if i.val < 2407 then
0
else
0)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
0
else
0)
else
(if i.val < 2411 then
0
else
0))
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
0))))
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
0
else
0))
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
0)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
0
else
0)
else
(if i.val < 2427 then
0
else
0))
else
(if i.val < 2430 then
(if i.val < 2429 then
0
else
0)
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
0
else
0)
else
(if i.val < 2435 then
0
else
0))
else
(if i.val < 2438 then
(if i.val < 2437 then
0
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
0
else
0)
else
(if i.val < 2443 then
0
else
0))
else
(if i.val < 2446 then
(if i.val < 2445 then
0
else
0)
else
(if i.val < 2447 then
0
else
0))))
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
0
else
0))
else
(if i.val < 2454 then
(if i.val < 2453 then
0
else
0)
else
(if i.val < 2455 then
0
else
0)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
0
else
0)
else
(if i.val < 2459 then
0
else
0))
else
(if i.val < 2462 then
(if i.val < 2461 then
0
else
0)
else
(if i.val < 2463 then
0
else
0)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
0
else
0)
else
(if i.val < 2467 then
0
else
0))
else
(if i.val < 2470 then
(if i.val < 2469 then
0
else
0)
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
0
else
0))
else
(if i.val < 2478 then
(if i.val < 2477 then
0
else
0)
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
0
else
0)
else
(if i.val < 2483 then
0
else
0))
else
(if i.val < 2486 then
(if i.val < 2485 then
0
else
0)
else
(if i.val < 2487 then
0
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
0
else
0))
else
(if i.val < 2494 then
(if i.val < 2493 then
0
else
0)
else
(if i.val < 2495 then
0
else
0))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
0
else
0)
else
(if i.val < 2499 then
0
else
0))
else
(if i.val < 2502 then
(if i.val < 2501 then
0
else
0)
else
(if i.val < 2503 then
0
else
0)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
0
else
0)
else
(if i.val < 2507 then
0
else
0))
else
(if i.val < 2510 then
(if i.val < 2509 then
0
else
0)
else
(if i.val < 2511 then
0
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
0
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
0)
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
0)
else
(if i.val < 2559 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end
