import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow04
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup02_source : Fin 1728 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 864 then (if i.val < 432 then (if i.val < 216 then (if i.val < 108 then (if i.val < 54 then (if i.val < 27 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (63, 240) else (70, 68))) else (if i.val < 4 then (128, 28) else (if i.val < 5 then (0, 97) else (111, 236)))) else (if i.val < 9 then (if i.val < 7 then (99, 188) else (if i.val < 8 then (14, 211) else (61, 91))) else (if i.val < 11 then (if i.val < 10 then (22, 28) else (84, 52)) else (if i.val < 12 then (70, 159) else (14, 88))))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then (13, 79) else (if i.val < 15 then (82, 136) else (56, 25))) else (if i.val < 18 then (if i.val < 17 then (11, 241) else (89, 228)) else (if i.val < 19 then (81, 86) else (86, 76)))) else (if i.val < 23 then (if i.val < 21 then (48, 52) else (if i.val < 22 then (20, 94) else (45, 143))) else (if i.val < 25 then (if i.val < 24 then (6, 17) else (139, 172)) else (if i.val < 26 then (6, 114) else (38, 204)))))) else (if i.val < 40 then (if i.val < 33 then (if i.val < 30 then (if i.val < 28 then (16, 144) else (if i.val < 29 then (94, 219) else (0, 101))) else (if i.val < 31 then (45, 102) else (if i.val < 32 then (126, 86) else (71, 89)))) else (if i.val < 36 then (if i.val < 34 then (22, 253) else (if i.val < 35 then (7, 136) else (107, 57))) else (if i.val < 38 then (if i.val < 37 then (62, 171) else (56, 124)) else (if i.val < 39 then (130, 180) else (33, 15))))) else (if i.val < 47 then (if i.val < 43 then (if i.val < 41 then (132, 85) else (if i.val < 42 then (0, 28) else (35, 93))) else (if i.val < 45 then (if i.val < 44 then (100, 198) else (80, 54)) else (if i.val < 46 then (60, 68) else (54, 175)))) else (if i.val < 50 then (if i.val < 48 then (79, 170) else (if i.val < 49 then (135, 209) else (83, 145))) else (if i.val < 52 then (if i.val < 51 then (132, 176) else (51, 202)) else (if i.val < 53 then (64, 178) else (135, 169))))))) else (if i.val < 81 then (if i.val < 67 then (if i.val < 60 then (if i.val < 57 then (if i.val < 55 then (31, 187) else (if i.val < 56 then (42, 123) else (69, 186))) else (if i.val < 58 then (97, 49) else (if i.val < 59 then (111, 7) else (117, 233)))) else (if i.val < 63 then (if i.val < 61 then (136, 226) else (if i.val < 62 then (90, 101) else (63, 1))) else (if i.val < 65 then (if i.val < 64 then (34, 178) else (60, 136)) else (if i.val < 66 then (101, 221) else (31, 197))))) else (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then (71, 9) else (if i.val < 69 then (54, 156) else (9, 66))) else (if i.val < 72 then (if i.val < 71 then (57, 215) else (73, 209)) else (if i.val < 73 then (87, 115) else (37, 102)))) else (if i.val < 77 then (if i.val < 75 then (10, 175) else (if i.val < 76 then (50, 170) else (12, 184))) else (if i.val < 79 then (if i.val < 78 then (66, 61) else (5, 133)) else (if i.val < 80 then (21, 144) else (88, 150)))))) else (if i.val < 94 then (if i.val < 87 then (if i.val < 84 then (if i.val < 82 then (99, 7) else (if i.val < 83 then (25, 30) else (103, 24))) else (if i.val < 85 then (112, 168) else (if i.val < 86 then (117, 61) else (59, 7)))) else (if i.val < 90 then (if i.val < 88 then (104, 7) else (if i.val < 89 then (1, 131) else (51, 188))) else (if i.val < 92 then (if i.val < 91 then (76, 76) else (81, 62)) else (if i.val < 93 then (13, 244) else (66, 190))))) else (if i.val < 101 then (if i.val < 97 then (if i.val < 95 then (52, 66) else (if i.val < 96 then (29, 235) else (113, 172))) else (if i.val < 99 then (if i.val < 98 then (75, 104) else (86, 206)) else (if i.val < 100 then (70, 162) else (71, 166)))) else (if i.val < 104 then (if i.val < 102 then (89, 97) else (if i.val < 103 then (7, 208) else (5, 158))) else (if i.val < 106 then (if i.val < 105 then (131, 191) else (140, 36)) else (if i.val < 107 then (124, 210) else (128, 96)))))))) else (if i.val < 162 then (if i.val < 135 then (if i.val < 121 then (if i.val < 114 then (if i.val < 111 then (if i.val < 109 then (86, 20) else (if i.val < 110 then (35, 13) else (55, 14))) else (if i.val < 112 then (13, 13) else (if i.val < 113 then (106, 139) else (111, 118)))) else (if i.val < 117 then (if i.val < 115 then (115, 169) else (if i.val < 116 then (111, 180) else (91, 64))) else (if i.val < 119 then (if i.val < 118 then (111, 108) else (77, 78)) else (if i.val < 120 then (68, 182) else (14, 214))))) else (if i.val < 128 then (if i.val < 124 then (if i.val < 122 then (79, 9) else (if i.val < 123 then (4, 49) else (104, 200))) else (if i.val < 126 then (if i.val < 125 then (39, 47) else (28, 205)) else (if i.val < 127 then (127, 194) else (29, 72)))) else (if i.val < 131 then (if i.val < 129 then (111, 244) else (if i.val < 130 then (141, 21) else (69, 213))) else (if i.val < 133 then (if i.val < 132 then (73, 244) else (132, 48)) else (if i.val < 134 then (37, 63) else (4, 13)))))) else (if i.val < 148 then (if i.val < 141 then (if i.val < 138 then (if i.val < 136 then (35, 6) else (if i.val < 137 then (24, 155) else (0, 99))) else (if i.val < 139 then (49, 59) else (if i.val < 140 then (132, 44) else (62, 140)))) else (if i.val < 144 then (if i.val < 142 then (97, 89) else (if i.val < 143 then (6, 109) else (86, 85))) else (if i.val < 146 then (if i.val < 145 then (86, 35) else (125, 209)) else (if i.val < 147 then (7, 214) else (101, 183))))) else (if i.val < 155 then (if i.val < 151 then (if i.val < 149 then (6, 94) else (if i.val < 150 then (126, 188) else (124, 229))) else (if i.val < 153 then (if i.val < 152 then (107, 198) else (6, 200)) else (if i.val < 154 then (11, 16) else (124, 144)))) else (if i.val < 158 then (if i.val < 156 then (115, 111) else (if i.val < 157 then (77, 150) else (80, 196))) else (if i.val < 160 then (if i.val < 159 then (122, 237) else (75, 110)) else (if i.val < 161 then (1, 174) else (124, 169))))))) else (if i.val < 189 then (if i.val < 175 then (if i.val < 168 then (if i.val < 165 then (if i.val < 163 then (103, 50) else (if i.val < 164 then (127, 234) else (49, 15))) else (if i.val < 166 then (84, 119) else (if i.val < 167 then (56, 67) else (10, 151)))) else (if i.val < 171 then (if i.val < 169 then (109, 228) else (if i.val < 170 then (102, 201) else (64, 184))) else (if i.val < 173 then (if i.val < 172 then (68, 56) else (129, 16)) else (if i.val < 174 then (100, 104) else (73, 238))))) else (if i.val < 182 then (if i.val < 178 then (if i.val < 176 then (5, 254) else (if i.val < 177 then (61, 25) else (139, 158))) else (if i.val < 180 then (if i.val < 179 then (81, 198) else (81, 48)) else (if i.val < 181 then (124, 184) else (12, 110)))) else (if i.val < 185 then (if i.val < 183 then (109, 254) else (if i.val < 184 then (101, 72) else (1, 172))) else (if i.val < 187 then (if i.val < 186 then (141, 117) else (107, 145)) else (if i.val < 188 then (55, 37) else (128, 23)))))) else (if i.val < 202 then (if i.val < 195 then (if i.val < 192 then (if i.val < 190 then (105, 72) else (if i.val < 191 then (47, 192) else (61, 204))) else (if i.val < 193 then (14, 237) else (if i.val < 194 then (57, 3) else (46, 155)))) else (if i.val < 198 then (if i.val < 196 then (14, 137) else (if i.val < 197 then (61, 187) else (105, 154))) else (if i.val < 200 then (if i.val < 199 then (38, 163) else (43, 74)) else (if i.val < 201 then (41, 5) else (104, 133))))) else (if i.val < 209 then (if i.val < 205 then (if i.val < 203 then (69, 228) else (if i.val < 204 then (125, 54) else (42, 144))) else (if i.val < 207 then (if i.val < 206 then (92, 80) else (31, 113)) else (if i.val < 208 then (109, 67) else (110, 86)))) else (if i.val < 212 then (if i.val < 210 then (6, 91) else (if i.val < 211 then (112, 164) else (66, 146))) else (if i.val < 214 then (if i.val < 213 then (10, 62) else (68, 241)) else (if i.val < 215 then (72, 79) else (100, 9))))))))) else (if i.val < 324 then (if i.val < 270 then (if i.val < 243 then (if i.val < 229 then (if i.val < 222 then (if i.val < 219 then (if i.val < 217 then (33, 193) else (if i.val < 218 then (94, 22) else (123, 134))) else (if i.val < 220 then (139, 137) else (if i.val < 221 then (122, 103) else (115, 189)))) else (if i.val < 225 then (if i.val < 223 then (52, 59) else (if i.val < 224 then (120, 181) else (120, 107))) else (if i.val < 227 then (if i.val < 226 then (113, 15) else (135, 207)) else (if i.val < 228 then (99, 23) else (73, 64))))) else (if i.val < 236 then (if i.val < 232 then (if i.val < 230 then (107, 242) else (if i.val < 231 then (86, 97) else (97, 232))) else (if i.val < 234 then (if i.val < 233 then (45, 231) else (23, 63)) else (if i.val < 235 then (3, 67) else (83, 132)))) else (if i.val < 239 then (if i.val < 237 then (74, 205) else (if i.val < 238 then (86, 200) else (107, 194))) else (if i.val < 241 then (if i.val < 240 then (25, 140) else (47, 109)) else (if i.val < 242 then (101, 186) else (61, 20)))))) else (if i.val < 256 then (if i.val < 249 then (if i.val < 246 then (if i.val < 244 then (79, 33) else (if i.val < 245 then (69, 166) else (32, 235))) else (if i.val < 247 then (34, 63) else (if i.val < 248 then (125, 93) else (61, 93)))) else (if i.val < 252 then (if i.val < 250 then (140, 127) else (if i.val < 251 then (122, 87) else (32, 102))) else (if i.val < 254 then (if i.val < 253 then (56, 88) else (118, 85)) else (if i.val < 255 then (58, 239) else (69, 144))))) else (if i.val < 263 then (if i.val < 259 then (if i.val < 257 then (11, 211) else (if i.val < 258 then (90, 13) else (105, 30))) else (if i.val < 261 then (if i.val < 260 then (122, 208) else (102, 177)) else (if i.val < 262 then (129, 232) else (105, 66)))) else (if i.val < 266 then (if i.val < 264 then (16, 29) else (if i.val < 265 then (75, 23) else (5, 59))) else (if i.val < 268 then (if i.val < 267 then (87, 153) else (44, 164)) else (if i.val < 269 then (61, 176) else (125, 218))))))) else (if i.val < 297 then (if i.val < 283 then (if i.val < 276 then (if i.val < 273 then (if i.val < 271 then (114, 240) else (if i.val < 272 then (93, 124) else (6, 195))) else (if i.val < 274 then (48, 254) else (if i.val < 275 then (99, 191) else (63, 112)))) else (if i.val < 279 then (if i.val < 277 then (12, 34) else (if i.val < 278 then (9, 235) else (4, 120))) else (if i.val < 281 then (if i.val < 280 then (37, 60) else (116, 39)) else (if i.val < 282 then (97, 6) else (92, 45))))) else (if i.val < 290 then (if i.val < 286 then (if i.val < 284 then (31, 184) else (if i.val < 285 then (88, 173) else (56, 153))) else (if i.val < 288 then (if i.val < 287 then (114, 24) else (37, 99)) else (if i.val < 289 then (112, 77) else (59, 218)))) else (if i.val < 293 then (if i.val < 291 then (100, 178) else (if i.val < 292 then (28, 96) else (135, 133))) else (if i.val < 295 then (if i.val < 294 then (14, 215) else (93, 161)) else (if i.val < 296 then (65, 236) else (122, 152)))))) else (if i.val < 310 then (if i.val < 303 then (if i.val < 300 then (if i.val < 298 then (5, 196) else (if i.val < 299 then (24, 86) else (93, 159))) else (if i.val < 301 then (102, 64) else (if i.val < 302 then (63, 174) else (106, 213)))) else (if i.val < 306 then (if i.val < 304 then (97, 108) else (if i.val < 305 then (50, 174) else (63, 183))) else (if i.val < 308 then (if i.val < 307 then (126, 70) else (113, 21)) else (if i.val < 309 then (96, 209) else (118, 8))))) else (if i.val < 317 then (if i.val < 313 then (if i.val < 311 then (84, 108) else (if i.val < 312 then (87, 190) else (105, 123))) else (if i.val < 315 then (if i.val < 314 then (64, 166) else (118, 249)) else (if i.val < 316 then (105, 69) else (119, 1)))) else (if i.val < 320 then (if i.val < 318 then (129, 188) else (if i.val < 319 then (106, 3) else (135, 134))) else (if i.val < 322 then (if i.val < 321 then (73, 13) else (70, 108)) else (if i.val < 323 then (94, 139) else (87, 134)))))))) else (if i.val < 378 then (if i.val < 351 then (if i.val < 337 then (if i.val < 330 then (if i.val < 327 then (if i.val < 325 then (113, 97) else (if i.val < 326 then (95, 244) else (129, 78))) else (if i.val < 328 then (141, 115) else (if i.val < 329 then (45, 156) else (122, 221)))) else (if i.val < 333 then (if i.val < 331 then (50, 141) else (if i.val < 332 then (106, 197) else (112, 20))) else (if i.val < 335 then (if i.val < 334 then (94, 79) else (113, 158)) else (if i.val < 336 then (20, 168) else (104, 4))))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then (12, 75) else (if i.val < 339 then (56, 247) else (126, 237))) else (if i.val < 342 then (if i.val < 341 then (105, 14) else (62, 172)) else (if i.val < 343 then (135, 69) else (65, 27)))) else (if i.val < 347 then (if i.val < 345 then (94, 17) else (if i.val < 346 then (90, 38) else (108, 5))) else (if i.val < 349 then (if i.val < 348 then (26, 104) else (14, 206)) else (if i.val < 350 then (60, 13) else (47, 17)))))) else (if i.val < 364 then (if i.val < 357 then (if i.val < 354 then (if i.val < 352 then (19, 207) else (if i.val < 353 then (105, 179) else (89, 41))) else (if i.val < 355 then (9, 108) else (if i.val < 356 then (15, 237) else (94, 15)))) else (if i.val < 360 then (if i.val < 358 then (80, 81) else (if i.val < 359 then (89, 93) else (108, 3))) else (if i.val < 362 then (if i.val < 361 then (107, 96) else (79, 71)) else (if i.val < 363 then (129, 79) else (80, 66))))) else (if i.val < 371 then (if i.val < 367 then (if i.val < 365 then (10, 221) else (if i.val < 366 then (78, 233) else (19, 92))) else (if i.val < 369 then (if i.val < 368 then (128, 144) else (16, 4)) else (if i.val < 370 then (23, 74) else (59, 62)))) else (if i.val < 374 then (if i.val < 372 then (46, 154) else (if i.val < 373 then (94, 183) else (91, 43))) else (if i.val < 376 then (if i.val < 375 then (57, 115) else (45, 2)) else (if i.val < 377 then (98, 165) else (76, 114))))))) else (if i.val < 405 then (if i.val < 391 then (if i.val < 384 then (if i.val < 381 then (if i.val < 379 then (119, 224) else (if i.val < 380 then (114, 147) else (74, 69))) else (if i.val < 382 then (20, 4) else (if i.val < 383 then (85, 109) else (118, 81)))) else (if i.val < 387 then (if i.val < 385 then (94, 225) else (if i.val < 386 then (97, 195) else (45, 248))) else (if i.val < 389 then (if i.val < 388 then (64, 241) else (74, 73)) else (if i.val < 390 then (37, 188) else (55, 198))))) else (if i.val < 398 then (if i.val < 394 then (if i.val < 392 then (38, 191) else (if i.val < 393 then (1, 167) else (26, 125))) else (if i.val < 396 then (if i.val < 395 then (129, 132) else (92, 109)) else (if i.val < 397 then (43, 181) else (33, 188)))) else (if i.val < 401 then (if i.val < 399 then (3, 66) else (if i.val < 400 then (32, 115) else (102, 216))) else (if i.val < 403 then (if i.val < 402 then (99, 214) else (106, 142)) else (if i.val < 404 then (55, 211) else (87, 108)))))) else (if i.val < 418 then (if i.val < 411 then (if i.val < 408 then (if i.val < 406 then (104, 60) else (if i.val < 407 then (89, 170) else (114, 152))) else (if i.val < 409 then (116, 211) else (if i.val < 410 then (78, 241) else (28, 10)))) else (if i.val < 414 then (if i.val < 412 then (15, 23) else (if i.val < 413 then (19, 81) else (141, 19))) else (if i.val < 416 then (if i.val < 415 then (57, 164) else (48, 215)) else (if i.val < 417 then (6, 186) else (114, 222))))) else (if i.val < 425 then (if i.val < 421 then (if i.val < 419 then (23, 141) else (if i.val < 420 then (28, 136) else (67, 135))) else (if i.val < 423 then (if i.val < 422 then (12, 92) else (56, 132)) else (if i.val < 424 then (61, 4) else (93, 186)))) else (if i.val < 428 then (if i.val < 426 then (44, 93) else (if i.val < 427 then (113, 121) else (14, 95))) else (if i.val < 430 then (if i.val < 429 then (123, 243) else (105, 248)) else (if i.val < 431 then (3, 8) else (20, 126)))))))))) else (if i.val < 648 then (if i.val < 540 then (if i.val < 486 then (if i.val < 459 then (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then (62, 167) else (if i.val < 434 then (102, 108) else (63, 246))) else (if i.val < 436 then (94, 138) else (if i.val < 437 then (20, 122) else (96, 50)))) else (if i.val < 441 then (if i.val < 439 then (130, 223) else (if i.val < 440 then (125, 129) else (51, 247))) else (if i.val < 443 then (if i.val < 442 then (79, 145) else (95, 85)) else (if i.val < 444 then (93, 211) else (79, 73))))) else (if i.val < 452 then (if i.val < 448 then (if i.val < 446 then (2, 106) else (if i.val < 447 then (118, 242) else (132, 60))) else (if i.val < 450 then (if i.val < 449 then (124, 160) else (126, 120)) else (if i.val < 451 then (54, 212) else (74, 204)))) else (if i.val < 455 then (if i.val < 453 then (134, 48) else (if i.val < 454 then (79, 188) else (6, 203))) else (if i.val < 457 then (if i.val < 456 then (91, 98) else (93, 73)) else (if i.val < 458 then (111, 81) else (69, 68)))))) else (if i.val < 472 then (if i.val < 465 then (if i.val < 462 then (if i.val < 460 then (18, 70) else (if i.val < 461 then (104, 6) else (81, 217))) else (if i.val < 463 then (85, 194) else (if i.val < 464 then (19, 121) else (53, 238)))) else (if i.val < 468 then (if i.val < 466 then (65, 4) else (if i.val < 467 then (73, 102) else (87, 159))) else (if i.val < 470 then (if i.val < 469 then (18, 198) else (105, 121)) else (if i.val < 471 then (56, 136) else (59, 208))))) else (if i.val < 479 then (if i.val < 475 then (if i.val < 473 then (62, 43) else (if i.val < 474 then (131, 195) else (15, 238))) else (if i.val < 477 then (if i.val < 476 then (33, 111) else (61, 192)) else (if i.val < 478 then (128, 158) else (108, 211)))) else (if i.val < 482 then (if i.val < 480 then (122, 105) else (if i.val < 481 then (16, 32) else (11, 93))) else (if i.val < 484 then (if i.val < 483 then (92, 221) else (84, 30)) else (if i.val < 485 then (75, 138) else (93, 170))))))) else (if i.val < 513 then (if i.val < 499 then (if i.val < 492 then (if i.val < 489 then (if i.val < 487 then (113, 185) else (if i.val < 488 then (115, 52) else (36, 151))) else (if i.val < 490 then (104, 254) else (if i.val < 491 then (68, 2) else (102, 50)))) else (if i.val < 495 then (if i.val < 493 then (76, 152) else (if i.val < 494 then (4, 69) else (95, 122))) else (if i.val < 497 then (if i.val < 496 then (134, 188) else (113, 248)) else (if i.val < 498 then (119, 119) else (122, 220))))) else (if i.val < 506 then (if i.val < 502 then (if i.val < 500 then (56, 38) else (if i.val < 501 then (121, 128) else (63, 43))) else (if i.val < 504 then (if i.val < 503 then (0, 96) else (39, 14)) else (if i.val < 505 then (87, 229) else (33, 59)))) else (if i.val < 509 then (if i.val < 507 then (80, 70) else (if i.val < 508 then (5, 142) else (87, 178))) else (if i.val < 511 then (if i.val < 510 then (24, 249) else (117, 204)) else (if i.val < 512 then (13, 148) else (5, 58)))))) else (if i.val < 526 then (if i.val < 519 then (if i.val < 516 then (if i.val < 514 then (5, 128) else (if i.val < 515 then (11, 19) else (86, 105))) else (if i.val < 517 then (102, 48) else (if i.val < 518 then (102, 35) else (33, 139)))) else (if i.val < 522 then (if i.val < 520 then (81, 61) else (if i.val < 521 then (89, 209) else (28, 244))) else (if i.val < 524 then (if i.val < 523 then (51, 224) else (118, 102)) else (if i.val < 525 then (29, 133) else (21, 167))))) else (if i.val < 533 then (if i.val < 529 then (if i.val < 527 then (128, 68) else (if i.val < 528 then (129, 3) else (12, 101))) else (if i.val < 531 then (if i.val < 530 then (102, 38) else (92, 188)) else (if i.val < 532 then (2, 16) else (49, 227)))) else (if i.val < 536 then (if i.val < 534 then (20, 249) else (if i.val < 535 then (10, 252) else (58, 70))) else (if i.val < 538 then (if i.val < 537 then (29, 3) else (60, 128)) else (if i.val < 539 then (30, 211) else (125, 4)))))))) else (if i.val < 594 then (if i.val < 567 then (if i.val < 553 then (if i.val < 546 then (if i.val < 543 then (if i.val < 541 then (12, 242) else (if i.val < 542 then (113, 120) else (19, 84))) else (if i.val < 544 then (108, 118) else (if i.val < 545 then (93, 184) else (127, 178)))) else (if i.val < 549 then (if i.val < 547 then (95, 83) else (if i.val < 548 then (86, 150) else (63, 226))) else (if i.val < 551 then (if i.val < 550 then (127, 182) else (96, 220)) else (if i.val < 552 then (109, 148) else (39, 204))))) else (if i.val < 560 then (if i.val < 556 then (if i.val < 554 then (11, 228) else (if i.val < 555 then (72, 195) else (108, 7))) else (if i.val < 558 then (if i.val < 557 then (60, 127) else (65, 225)) else (if i.val < 559 then (11, 127) else (72, 76)))) else (if i.val < 563 then (if i.val < 561 then (9, 232) else (if i.val < 562 then (85, 142) else (84, 171))) else (if i.val < 565 then (if i.val < 564 then (88, 61) else (112, 23)) else (if i.val < 566 then (90, 249) else (78, 144)))))) else (if i.val < 580 then (if i.val < 573 then (if i.val < 570 then (if i.val < 568 then (49, 225) else (if i.val < 569 then (100, 251) else (126, 33))) else (if i.val < 571 then (129, 121) else (if i.val < 572 then (104, 250) else (10, 235)))) else (if i.val < 576 then (if i.val < 574 then (87, 43) else (if i.val < 575 then (98, 70) else (138, 53))) else (if i.val < 578 then (if i.val < 577 then (139, 251) else (85, 243)) else (if i.val < 579 then (85, 145) else (77, 162))))) else (if i.val < 587 then (if i.val < 583 then (if i.val < 581 then (50, 76) else (if i.val < 582 then (58, 100) else (2, 96))) else (if i.val < 585 then (if i.val < 584 then (97, 248) else (58, 129)) else (if i.val < 586 then (26, 216) else (38, 183)))) else (if i.val < 590 then (if i.val < 588 then (106, 241) else (if i.val < 589 then (95, 64) else (128, 177))) else (if i.val < 592 then (if i.val < 591 then (56, 225) else (32, 96)) else (if i.val < 593 then (66, 96) else (112, 250))))))) else (if i.val < 621 then (if i.val < 607 then (if i.val < 600 then (if i.val < 597 then (if i.val < 595 then (112, 196) else (if i.val < 596 then (54, 207) else (88, 72))) else (if i.val < 598 then (85, 214) else (if i.val < 599 then (115, 168) else (9, 121)))) else (if i.val < 603 then (if i.val < 601 then (67, 236) else (if i.val < 602 then (66, 93) else (127, 6))) else (if i.val < 605 then (if i.val < 604 then (118, 30) else (123, 177)) else (if i.val < 606 then (109, 99) else (74, 120))))) else (if i.val < 614 then (if i.val < 610 then (if i.val < 608 then (5, 190) else (if i.val < 609 then (60, 144) else (35, 169))) else (if i.val < 612 then (if i.val < 611 then (23, 88) else (95, 67)) else (if i.val < 613 then (140, 203) else (101, 16)))) else (if i.val < 617 then (if i.val < 615 then (74, 244) else (if i.val < 616 then (58, 24) else (118, 190))) else (if i.val < 619 then (if i.val < 618 then (87, 55) else (55, 214)) else (if i.val < 620 then (10, 50) else (47, 146)))))) else (if i.val < 634 then (if i.val < 627 then (if i.val < 624 then (if i.val < 622 then (113, 135) else (if i.val < 623 then (58, 99) else (119, 164))) else (if i.val < 625 then (72, 3) else (if i.val < 626 then (116, 245) else (139, 148)))) else (if i.val < 630 then (if i.val < 628 then (48, 7) else (if i.val < 629 then (63, 95) else (84, 176))) else (if i.val < 632 then (if i.val < 631 then (28, 122) else (73, 24)) else (if i.val < 633 then (60, 151) else (107, 184))))) else (if i.val < 641 then (if i.val < 637 then (if i.val < 635 then (77, 217) else (if i.val < 636 then (84, 160) else (61, 225))) else (if i.val < 639 then (if i.val < 638 then (23, 189) else (5, 106)) else (if i.val < 640 then (31, 106) else (119, 91)))) else (if i.val < 644 then (if i.val < 642 then (131, 17) else (if i.val < 643 then (136, 129) else (71, 93))) else (if i.val < 646 then (if i.val < 645 then (114, 86) else (29, 185)) else (if i.val < 647 then (24, 28) else (5, 49))))))))) else (if i.val < 756 then (if i.val < 702 then (if i.val < 675 then (if i.val < 661 then (if i.val < 654 then (if i.val < 651 then (if i.val < 649 then (131, 21) else (if i.val < 650 then (85, 44) else (1, 152))) else (if i.val < 652 then (4, 219) else (if i.val < 653 then (72, 48) else (11, 132)))) else (if i.val < 657 then (if i.val < 655 then (38, 197) else (if i.val < 656 then (61, 191) else (112, 12))) else (if i.val < 659 then (if i.val < 658 then (83, 191) else (57, 52)) else (if i.val < 660 then (88, 210) else (140, 141))))) else (if i.val < 668 then (if i.val < 664 then (if i.val < 662 then (100, 218) else (if i.val < 663 then (126, 109) else (81, 158))) else (if i.val < 666 then (if i.val < 665 then (24, 210) else (100, 166)) else (if i.val < 667 then (133, 202) else (11, 164)))) else (if i.val < 671 then (if i.val < 669 then (116, 31) else (if i.val < 670 then (96, 59) else (75, 212))) else (if i.val < 673 then (if i.val < 672 then (140, 188) else (47, 220)) else (if i.val < 674 then (49, 54) else (58, 75)))))) else (if i.val < 688 then (if i.val < 681 then (if i.val < 678 then (if i.val < 676 then (98, 89) else (if i.val < 677 then (28, 5) else (9, 134))) else (if i.val < 679 then (0, 223) else (if i.val < 680 then (96, 134) else (111, 129)))) else (if i.val < 684 then (if i.val < 682 then (99, 96) else (if i.val < 683 then (126, 201) else (41, 207))) else (if i.val < 686 then (if i.val < 685 then (114, 4) else (46, 253)) else (if i.val < 687 then (133, 98) else (56, 20))))) else (if i.val < 695 then (if i.val < 691 then (if i.val < 689 then (74, 132) else (if i.val < 690 then (127, 233) else (19, 164))) else (if i.val < 693 then (if i.val < 692 then (96, 201) else (20, 245)) else (if i.val < 694 then (33, 144) else (48, 218)))) else (if i.val < 698 then (if i.val < 696 then (64, 76) else (if i.val < 697 then (5, 98) else (56, 110))) else (if i.val < 700 then (if i.val < 699 then (69, 33) else (4, 192)) else (if i.val < 701 then (122, 224) else (110, 218))))))) else (if i.val < 729 then (if i.val < 715 then (if i.val < 708 then (if i.val < 705 then (if i.val < 703 then (114, 242) else (if i.val < 704 then (82, 71) else (124, 130))) else (if i.val < 706 then (5, 66) else (if i.val < 707 then (57, 70) else (89, 25)))) else (if i.val < 711 then (if i.val < 709 then (86, 98) else (if i.val < 710 then (49, 191) else (117, 192))) else (if i.val < 713 then (if i.val < 712 then (98, 57) else (1, 76)) else (if i.val < 714 then (131, 9) else (92, 24))))) else (if i.val < 722 then (if i.val < 718 then (if i.val < 716 then (85, 68) else (if i.val < 717 then (80, 163) else (94, 78))) else (if i.val < 720 then (if i.val < 719 then (29, 158) else (74, 13)) else (if i.val < 721 then (111, 124) else (43, 83)))) else (if i.val < 725 then (if i.val < 723 then (99, 95) else (if i.val < 724 then (98, 68) else (128, 242))) else (if i.val < 727 then (if i.val < 726 then (100, 161) else (82, 19)) else (if i.val < 728 then (55, 75) else (46, 121)))))) else (if i.val < 742 then (if i.val < 735 then (if i.val < 732 then (if i.val < 730 then (44, 140) else (if i.val < 731 then (72, 238) else (138, 249))) else (if i.val < 733 then (62, 191) else (if i.val < 734 then (83, 197) else (29, 157)))) else (if i.val < 738 then (if i.val < 736 then (71, 5) else (if i.val < 737 then (103, 77) else (126, 186))) else (if i.val < 740 then (if i.val < 739 then (135, 129) else (26, 97)) else (if i.val < 741 then (51, 207) else (115, 119))))) else (if i.val < 749 then (if i.val < 745 then (if i.val < 743 then (1, 120) else (if i.val < 744 then (96, 251) else (80, 106))) else (if i.val < 747 then (if i.val < 746 then (108, 146) else (84, 118)) else (if i.val < 748 then (105, 103) else (17, 89)))) else (if i.val < 752 then (if i.val < 750 then (112, 45) else (if i.val < 751 then (76, 247) else (140, 151))) else (if i.val < 754 then (if i.val < 753 then (85, 219) else (65, 54)) else (if i.val < 755 then (116, 174) else (5, 79)))))))) else (if i.val < 810 then (if i.val < 783 then (if i.val < 769 then (if i.val < 762 then (if i.val < 759 then (if i.val < 757 then (46, 203) else (if i.val < 758 then (44, 61) else (30, 40))) else (if i.val < 760 then (45, 186) else (if i.val < 761 then (98, 191) else (31, 123)))) else (if i.val < 765 then (if i.val < 763 then (119, 172) else (if i.val < 764 then (74, 105) else (51, 5))) else (if i.val < 767 then (if i.val < 766 then (131, 213) else (60, 204)) else (if i.val < 768 then (135, 205) else (35, 16))))) else (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then (73, 250) else (if i.val < 771 then (106, 247) else (100, 53))) else (if i.val < 774 then (if i.val < 773 then (89, 53) else (58, 22)) else (if i.val < 775 then (45, 90) else (111, 58)))) else (if i.val < 779 then (if i.val < 777 then (59, 1) else (if i.val < 778 then (75, 179) else (85, 226))) else (if i.val < 781 then (if i.val < 780 then (119, 0) else (132, 36)) else (if i.val < 782 then (96, 177) else (7, 205)))))) else (if i.val < 796 then (if i.val < 789 then (if i.val < 786 then (if i.val < 784 then (4, 128) else (if i.val < 785 then (90, 215) else (17, 84))) else (if i.val < 787 then (105, 134) else (if i.val < 788 then (98, 99) else (91, 204)))) else (if i.val < 792 then (if i.val < 790 then (132, 47) else (if i.val < 791 then (95, 66) else (116, 111))) else (if i.val < 794 then (if i.val < 793 then (109, 193) else (55, 35)) else (if i.val < 795 then (54, 239) else (130, 206))))) else (if i.val < 803 then (if i.val < 799 then (if i.val < 797 then (106, 111) else (if i.val < 798 then (47, 103) else (79, 159))) else (if i.val < 801 then (if i.val < 800 then (82, 162) else (105, 196)) else (if i.val < 802 then (39, 143) else (141, 145)))) else (if i.val < 806 then (if i.val < 804 then (25, 32) else (if i.val < 805 then (28, 86) else (84, 25))) else (if i.val < 808 then (if i.val < 807 then (58, 235) else (56, 17)) else (if i.val < 809 then (102, 76) else (105, 67))))))) else (if i.val < 837 then (if i.val < 823 then (if i.val < 816 then (if i.val < 813 then (if i.val < 811 then (114, 164) else (if i.val < 812 then (102, 130) else (128, 82))) else (if i.val < 814 then (139, 248) else (if i.val < 815 then (117, 196) else (103, 149)))) else (if i.val < 819 then (if i.val < 817 then (14, 7) else (if i.val < 818 then (56, 99) else (112, 70))) else (if i.val < 821 then (if i.val < 820 then (57, 136) else (110, 115)) else (if i.val < 822 then (55, 4) else (34, 196))))) else (if i.val < 830 then (if i.val < 826 then (if i.val < 824 then (89, 105) else (if i.val < 825 then (111, 30) else (26, 34))) else (if i.val < 828 then (if i.val < 827 then (105, 152) else (133, 36)) else (if i.val < 829 then (77, 230) else (69, 87)))) else (if i.val < 833 then (if i.val < 831 then (60, 141) else (if i.val < 832 then (142, 11) else (34, 248))) else (if i.val < 835 then (if i.val < 834 then (66, 161) else (89, 83)) else (if i.val < 836 then (86, 110) else (83, 208)))))) else (if i.val < 850 then (if i.val < 843 then (if i.val < 840 then (if i.val < 838 then (56, 34) else (if i.val < 839 then (130, 81) else (102, 171))) else (if i.val < 841 then (55, 78) else (if i.val < 842 then (14, 176) else (125, 187)))) else (if i.val < 846 then (if i.val < 844 then (28, 165) else (if i.val < 845 then (106, 42) else (129, 183))) else (if i.val < 848 then (if i.val < 847 then (108, 48) else (27, 16)) else (if i.val < 849 then (76, 205) else (58, 238))))) else (if i.val < 857 then (if i.val < 853 then (if i.val < 851 then (14, 157) else (if i.val < 852 then (34, 37) else (102, 204))) else (if i.val < 855 then (if i.val < 854 then (31, 149) else (105, 54)) else (if i.val < 856 then (99, 154) else (27, 35)))) else (if i.val < 860 then (if i.val < 858 then (14, 94) else (if i.val < 859 then (53, 160) else (139, 157))) else (if i.val < 862 then (if i.val < 861 then (4, 17) else (114, 114)) else (if i.val < 863 then (142, 123) else (105, 228))))))))))) else (if i.val < 1296 then (if i.val < 1080 then (if i.val < 972 then (if i.val < 918 then (if i.val < 891 then (if i.val < 877 then (if i.val < 870 then (if i.val < 867 then (if i.val < 865 then (45, 19) else (if i.val < 866 then (113, 155) else (34, 240))) else (if i.val < 868 then (45, 252) else (if i.val < 869 then (77, 36) else (63, 164)))) else (if i.val < 873 then (if i.val < 871 then (85, 107) else (if i.val < 872 then (116, 255) else (124, 186))) else (if i.val < 875 then (if i.val < 874 then (24, 190) else (127, 176)) else (if i.val < 876 then (49, 10) else (134, 46))))) else (if i.val < 884 then (if i.val < 880 then (if i.val < 878 then (65, 147) else (if i.val < 879 then (29, 41) else (76, 112))) else (if i.val < 882 then (if i.val < 881 then (35, 57) else (112, 52)) else (if i.val < 883 then (39, 193) else (93, 153)))) else (if i.val < 887 then (if i.val < 885 then (122, 232) else (if i.val < 886 then (118, 246) else (31, 105))) else (if i.val < 889 then (if i.val < 888 then (14, 172) else (5, 65)) else (if i.val < 890 then (135, 203) else (108, 69)))))) else (if i.val < 904 then (if i.val < 897 then (if i.val < 894 then (if i.val < 892 then (129, 13) else (if i.val < 893 then (59, 72) else (98, 233))) else (if i.val < 895 then (33, 106) else (if i.val < 896 then (58, 102) else (34, 0)))) else (if i.val < 900 then (if i.val < 898 then (67, 165) else (if i.val < 899 then (73, 99) else (40, 25))) else (if i.val < 902 then (if i.val < 901 then (65, 183) else (44, 247)) else (if i.val < 903 then (45, 239) else (139, 72))))) else (if i.val < 911 then (if i.val < 907 then (if i.val < 905 then (36, 110) else (if i.val < 906 then (29, 49) else (35, 125))) else (if i.val < 909 then (if i.val < 908 then (35, 201) else (60, 238)) else (if i.val < 910 then (116, 221) else (56, 15)))) else (if i.val < 914 then (if i.val < 912 then (82, 41) else (if i.val < 913 then (59, 86) else (17, 205))) else (if i.val < 916 then (if i.val < 915 then (120, 253) else (77, 202)) else (if i.val < 917 then (32, 103) else (34, 116))))))) else (if i.val < 945 then (if i.val < 931 then (if i.val < 924 then (if i.val < 921 then (if i.val < 919 then (79, 166) else (if i.val < 920 then (83, 74) else (31, 156))) else (if i.val < 922 then (111, 186) else (if i.val < 923 then (69, 155) else (87, 152)))) else (if i.val < 927 then (if i.val < 925 then (35, 255) else (if i.val < 926 then (115, 130) else (49, 91))) else (if i.val < 929 then (if i.val < 928 then (140, 171) else (92, 36)) else (if i.val < 930 then (20, 76) else (109, 104))))) else (if i.val < 938 then (if i.val < 934 then (if i.val < 932 then (82, 26) else (if i.val < 933 then (50, 65) else (39, 152))) else (if i.val < 936 then (if i.val < 935 then (10, 91) else (14, 242)) else (if i.val < 937 then (57, 243) else (34, 247)))) else (if i.val < 941 then (if i.val < 939 then (109, 49) else (if i.val < 940 then (44, 117) else (5, 151))) else (if i.val < 943 then (if i.val < 942 then (66, 51) else (74, 190)) else (if i.val < 944 then (52, 57) else (55, 220)))))) else (if i.val < 958 then (if i.val < 951 then (if i.val < 948 then (if i.val < 946 then (39, 229) else (if i.val < 947 then (8, 27) else (50, 215))) else (if i.val < 949 then (36, 70) else (if i.val < 950 then (35, 194) else (64, 126)))) else (if i.val < 954 then (if i.val < 952 then (52, 213) else (if i.val < 953 then (80, 120) else (1, 85))) else (if i.val < 956 then (if i.val < 955 then (100, 133) else (67, 169)) else (if i.val < 957 then (110, 124) else (53, 68))))) else (if i.val < 965 then (if i.val < 961 then (if i.val < 959 then (108, 85) else (if i.val < 960 then (110, 91) else (46, 67))) else (if i.val < 963 then (if i.val < 962 then (39, 172) else (132, 145)) else (if i.val < 964 then (138, 150) else (75, 217)))) else (if i.val < 968 then (if i.val < 966 then (129, 14) else (if i.val < 967 then (43, 34) else (44, 15))) else (if i.val < 970 then (if i.val < 969 then (11, 8) else (133, 23)) else (if i.val < 971 then (91, 81) else (74, 54)))))))) else (if i.val < 1026 then (if i.val < 999 then (if i.val < 985 then (if i.val < 978 then (if i.val < 975 then (if i.val < 973 then (27, 159) else (if i.val < 974 then (129, 196) else (66, 75))) else (if i.val < 976 then (55, 128) else (if i.val < 977 then (73, 159) else (139, 29)))) else (if i.val < 981 then (if i.val < 979 then (50, 191) else (if i.val < 980 then (51, 236) else (95, 214))) else (if i.val < 983 then (if i.val < 982 then (34, 180) else (7, 199)) else (if i.val < 984 then (40, 67) else (45, 179))))) else (if i.val < 992 then (if i.val < 988 then (if i.val < 986 then (87, 198) else (if i.val < 987 then (105, 173) else (45, 163))) else (if i.val < 990 then (if i.val < 989 then (124, 252) else (113, 154)) else (if i.val < 991 then (90, 55) else (14, 197)))) else (if i.val < 995 then (if i.val < 993 then (98, 116) else (if i.val < 994 then (38, 44) else (15, 227))) else (if i.val < 997 then (if i.val < 996 then (62, 217) else (128, 208)) else (if i.val < 998 then (110, 142) else (17, 115)))))) else (if i.val < 1012 then (if i.val < 1005 then (if i.val < 1002 then (if i.val < 1000 then (122, 0) else (if i.val < 1001 then (90, 131) else (124, 91))) else (if i.val < 1003 then (91, 73) else (if i.val < 1004 then (54, 35) else (50, 254)))) else (if i.val < 1008 then (if i.val < 1006 then (92, 234) else (if i.val < 1007 then (70, 246) else (1, 149))) else (if i.val < 1010 then (if i.val < 1009 then (27, 187) else (125, 67)) else (if i.val < 1011 then (22, 153) else (110, 13))))) else (if i.val < 1019 then (if i.val < 1015 then (if i.val < 1013 then (61, 206) else (if i.val < 1014 then (112, 165) else (86, 139))) else (if i.val < 1017 then (if i.val < 1016 then (6, 73) else (93, 135)) else (if i.val < 1018 then (133, 190) else (67, 9)))) else (if i.val < 1022 then (if i.val < 1020 then (95, 24) else (if i.val < 1021 then (80, 192) else (21, 158))) else (if i.val < 1024 then (if i.val < 1023 then (98, 115) else (55, 73)) else (if i.val < 1025 then (94, 88) else (79, 190))))))) else (if i.val < 1053 then (if i.val < 1039 then (if i.val < 1032 then (if i.val < 1029 then (if i.val < 1027 then (42, 39) else (if i.val < 1028 then (113, 157) else (113, 106))) else (if i.val < 1030 then (5, 22) else (if i.val < 1031 then (41, 7) else (48, 20)))) else (if i.val < 1035 then (if i.val < 1033 then (69, 157) else (if i.val < 1034 then (108, 152) else (33, 47))) else (if i.val < 1037 then (if i.val < 1036 then (26, 81) else (28, 197)) else (if i.val < 1038 then (108, 56) else (26, 103))))) else (if i.val < 1046 then (if i.val < 1042 then (if i.val < 1040 then (32, 234) else (if i.val < 1041 then (136, 138) else (74, 106))) else (if i.val < 1044 then (if i.val < 1043 then (79, 254) else (88, 116)) else (if i.val < 1045 then (139, 97) else (56, 8)))) else (if i.val < 1049 then (if i.val < 1047 then (106, 100) else (if i.val < 1048 then (85, 116) else (130, 98))) else (if i.val < 1051 then (if i.val < 1050 then (126, 123) else (83, 89)) else (if i.val < 1052 then (30, 171) else (97, 183)))))) else (if i.val < 1066 then (if i.val < 1059 then (if i.val < 1056 then (if i.val < 1054 then (78, 249) else (if i.val < 1055 then (81, 247) else (45, 71))) else (if i.val < 1057 then (123, 71) else (if i.val < 1058 then (88, 102) else (104, 106)))) else (if i.val < 1062 then (if i.val < 1060 then (67, 33) else (if i.val < 1061 then (13, 253) else (73, 181))) else (if i.val < 1064 then (if i.val < 1063 then (33, 21) else (121, 118)) else (if i.val < 1065 then (14, 244) else (86, 247))))) else (if i.val < 1073 then (if i.val < 1069 then (if i.val < 1067 then (65, 124) else (if i.val < 1068 then (33, 49) else (60, 25))) else (if i.val < 1071 then (if i.val < 1070 then (73, 165) else (105, 192)) else (if i.val < 1072 then (91, 241) else (56, 39)))) else (if i.val < 1076 then (if i.val < 1074 then (83, 85) else (if i.val < 1075 then (5, 80) else (85, 150))) else (if i.val < 1078 then (if i.val < 1077 then (68, 5) else (102, 121)) else (if i.val < 1079 then (128, 110) else (31, 80))))))))) else (if i.val < 1188 then (if i.val < 1134 then (if i.val < 1107 then (if i.val < 1093 then (if i.val < 1086 then (if i.val < 1083 then (if i.val < 1081 then (127, 131) else (if i.val < 1082 then (115, 123) else (58, 123))) else (if i.val < 1084 then (36, 102) else (if i.val < 1085 then (53, 58) else (42, 225)))) else (if i.val < 1089 then (if i.val < 1087 then (53, 118) else (if i.val < 1088 then (47, 160) else (14, 93))) else (if i.val < 1091 then (if i.val < 1090 then (110, 213) else (104, 3)) else (if i.val < 1092 then (98, 235) else (61, 140))))) else (if i.val < 1100 then (if i.val < 1096 then (if i.val < 1094 then (4, 107) else (if i.val < 1095 then (57, 148) else (74, 5))) else (if i.val < 1098 then (if i.val < 1097 then (94, 185) else (53, 198)) else (if i.val < 1099 then (97, 103) else (92, 31)))) else (if i.val < 1103 then (if i.val < 1101 then (121, 174) else (if i.val < 1102 then (34, 212) else (71, 79))) else (if i.val < 1105 then (if i.val < 1104 then (104, 45) else (84, 29)) else (if i.val < 1106 then (125, 204) else (58, 231)))))) else (if i.val < 1120 then (if i.val < 1113 then (if i.val < 1110 then (if i.val < 1108 then (126, 51) else (if i.val < 1109 then (71, 97) else (132, 144))) else (if i.val < 1111 then (115, 108) else (if i.val < 1112 then (82, 200) else (119, 107)))) else (if i.val < 1116 then (if i.val < 1114 then (57, 206) else (if i.val < 1115 then (98, 172) else (66, 119))) else (if i.val < 1118 then (if i.val < 1117 then (54, 177) else (25, 242)) else (if i.val < 1119 then (138, 78) else (88, 118))))) else (if i.val < 1127 then (if i.val < 1123 then (if i.val < 1121 then (49, 197) else (if i.val < 1122 then (101, 5) else (79, 149))) else (if i.val < 1125 then (if i.val < 1124 then (41, 212) else (96, 232)) else (if i.val < 1126 then (115, 227) else (123, 32)))) else (if i.val < 1130 then (if i.val < 1128 then (75, 178) else (if i.val < 1129 then (5, 71) else (28, 170))) else (if i.val < 1132 then (if i.val < 1131 then (54, 79) else (115, 181)) else (if i.val < 1133 then (65, 10) else (35, 236))))))) else (if i.val < 1161 then (if i.val < 1147 then (if i.val < 1140 then (if i.val < 1137 then (if i.val < 1135 then (40, 66) else (if i.val < 1136 then (137, 128) else (102, 172))) else (if i.val < 1138 then (67, 74) else (if i.val < 1139 then (37, 13) else (64, 99)))) else (if i.val < 1143 then (if i.val < 1141 then (123, 88) else (if i.val < 1142 then (116, 128) else (40, 179))) else (if i.val < 1145 then (if i.val < 1144 then (115, 174) else (94, 96)) else (if i.val < 1146 then (44, 244) else (121, 212))))) else (if i.val < 1154 then (if i.val < 1150 then (if i.val < 1148 then (31, 115) else (if i.val < 1149 then (57, 134) else (140, 21))) else (if i.val < 1152 then (if i.val < 1151 then (53, 59) else (43, 93)) else (if i.val < 1153 then (116, 118) else (106, 4)))) else (if i.val < 1157 then (if i.val < 1155 then (32, 243) else (if i.val < 1156 then (87, 221) else (112, 159))) else (if i.val < 1159 then (if i.val < 1158 then (40, 158) else (59, 4)) else (if i.val < 1160 then (90, 26) else (100, 225)))))) else (if i.val < 1174 then (if i.val < 1167 then (if i.val < 1164 then (if i.val < 1162 then (133, 175) else (if i.val < 1163 then (65, 234) else (123, 42))) else (if i.val < 1165 then (120, 7) else (if i.val < 1166 then (53, 19) else (34, 98)))) else (if i.val < 1170 then (if i.val < 1168 then (103, 240) else (if i.val < 1169 then (85, 117) else (66, 50))) else (if i.val < 1172 then (if i.val < 1171 then (137, 103) else (41, 38)) else (if i.val < 1173 then (125, 121) else (92, 239))))) else (if i.val < 1181 then (if i.val < 1177 then (if i.val < 1175 then (44, 57) else (if i.val < 1176 then (110, 33) else (108, 119))) else (if i.val < 1179 then (if i.val < 1178 then (29, 147) else (101, 97)) else (if i.val < 1180 then (68, 130) else (87, 133)))) else (if i.val < 1184 then (if i.val < 1182 then (48, 252) else (if i.val < 1183 then (6, 75) else (93, 109))) else (if i.val < 1186 then (if i.val < 1185 then (122, 150) else (81, 248)) else (if i.val < 1187 then (96, 172) else (91, 44)))))))) else (if i.val < 1242 then (if i.val < 1215 then (if i.val < 1201 then (if i.val < 1194 then (if i.val < 1191 then (if i.val < 1189 then (102, 224) else (if i.val < 1190 then (119, 133) else (119, 83))) else (if i.val < 1192 then (99, 184) else (if i.val < 1193 then (39, 25) else (125, 12)))) else (if i.val < 1197 then (if i.val < 1195 then (58, 101) else (if i.val < 1196 then (60, 34) else (3, 239))) else (if i.val < 1199 then (if i.val < 1198 then (136, 150) else (61, 237)) else (if i.val < 1200 then (110, 199) else (98, 202))))) else (if i.val < 1208 then (if i.val < 1204 then (if i.val < 1202 then (82, 152) else (if i.val < 1203 then (132, 3) else (123, 22))) else (if i.val < 1206 then (if i.val < 1205 then (113, 71) else (89, 21)) else (if i.val < 1207 then (0, 37) else (83, 118)))) else (if i.val < 1211 then (if i.val < 1209 then (56, 154) else (if i.val < 1210 then (128, 38) else (128, 221))) else (if i.val < 1213 then (if i.val < 1212 then (5, 195) else (124, 36)) else (if i.val < 1214 then (130, 222) else (118, 4)))))) else (if i.val < 1228 then (if i.val < 1221 then (if i.val < 1218 then (if i.val < 1216 then (118, 176) else (if i.val < 1217 then (7, 8) else (123, 250))) else (if i.val < 1219 then (123, 17) else (if i.val < 1220 then (94, 144) else (99, 216)))) else (if i.val < 1224 then (if i.val < 1222 then (49, 236) else (if i.val < 1223 then (102, 6) else (2, 103))) else (if i.val < 1226 then (if i.val < 1225 then (109, 218) else (100, 149)) else (if i.val < 1227 then (124, 139) else (129, 164))))) else (if i.val < 1235 then (if i.val < 1231 then (if i.val < 1229 then (96, 214) else (if i.val < 1230 then (136, 101) else (6, 239))) else (if i.val < 1233 then (if i.val < 1232 then (97, 220) else (34, 186)) else (if i.val < 1234 then (88, 91) else (101, 7)))) else (if i.val < 1238 then (if i.val < 1236 then (135, 82) else (if i.val < 1237 then (94, 146) else (101, 149))) else (if i.val < 1240 then (if i.val < 1239 then (123, 86) else (55, 174)) else (if i.val < 1241 then (37, 154) else (83, 164))))))) else (if i.val < 1269 then (if i.val < 1255 then (if i.val < 1248 then (if i.val < 1245 then (if i.val < 1243 then (40, 171) else (if i.val < 1244 then (87, 70) else (89, 211))) else (if i.val < 1246 then (56, 143) else (if i.val < 1247 then (62, 109) else (70, 20)))) else (if i.val < 1251 then (if i.val < 1249 then (120, 176) else (if i.val < 1250 then (73, 195) else (36, 26))) else (if i.val < 1253 then (if i.val < 1252 then (65, 35) else (108, 201)) else (if i.val < 1254 then (66, 219) else (93, 15))))) else (if i.val < 1262 then (if i.val < 1258 then (if i.val < 1256 then (1, 227) else (if i.val < 1257 then (138, 114) else (121, 2))) else (if i.val < 1260 then (if i.val < 1259 then (58, 252) else (98, 119)) else (if i.val < 1261 then (121, 215) else (11, 232)))) else (if i.val < 1265 then (if i.val < 1263 then (4, 83) else (if i.val < 1264 then (120, 186) else (9, 253))) else (if i.val < 1267 then (if i.val < 1266 then (17, 183) else (88, 90)) else (if i.val < 1268 then (135, 174) else (132, 153)))))) else (if i.val < 1282 then (if i.val < 1275 then (if i.val < 1272 then (if i.val < 1270 then (60, 180) else (if i.val < 1271 then (45, 182) else (101, 200))) else (if i.val < 1273 then (129, 180) else (if i.val < 1274 then (1, 236) else (122, 115)))) else (if i.val < 1278 then (if i.val < 1276 then (60, 28) else (if i.val < 1277 then (55, 65) else (62, 124))) else (if i.val < 1280 then (if i.val < 1279 then (56, 57) else (82, 158)) else (if i.val < 1281 then (124, 135) else (135, 89))))) else (if i.val < 1289 then (if i.val < 1285 then (if i.val < 1283 then (105, 178) else (if i.val < 1284 then (95, 135) else (137, 18))) else (if i.val < 1287 then (if i.val < 1286 then (59, 84) else (124, 133)) else (if i.val < 1288 then (20, 172) else (125, 203)))) else (if i.val < 1292 then (if i.val < 1290 then (5, 194) else (if i.val < 1291 then (107, 65) else (54, 204))) else (if i.val < 1294 then (if i.val < 1293 then (126, 159) else (53, 65)) else (if i.val < 1295 then (127, 201) else (85, 187)))))))))) else (if i.val < 1512 then (if i.val < 1404 then (if i.val < 1350 then (if i.val < 1323 then (if i.val < 1309 then (if i.val < 1302 then (if i.val < 1299 then (if i.val < 1297 then (64, 144) else (if i.val < 1298 then (52, 76) else (107, 171))) else (if i.val < 1300 then (111, 79) else (if i.val < 1301 then (28, 188) else (28, 35)))) else (if i.val < 1305 then (if i.val < 1303 then (65, 2) else (if i.val < 1304 then (102, 12) else (119, 40))) else (if i.val < 1307 then (if i.val < 1306 then (83, 178) else (115, 61)) else (if i.val < 1308 then (111, 208) else (54, 87))))) else (if i.val < 1316 then (if i.val < 1312 then (if i.val < 1310 then (64, 135) else (if i.val < 1311 then (1, 99) else (88, 83))) else (if i.val < 1314 then (if i.val < 1313 then (97, 154) else (80, 104)) else (if i.val < 1315 then (5, 141) else (62, 76)))) else (if i.val < 1319 then (if i.val < 1317 then (98, 61) else (if i.val < 1318 then (109, 233) else (48, 69))) else (if i.val < 1321 then (if i.val < 1320 then (107, 146) else (30, 213)) else (if i.val < 1322 then (124, 54) else (59, 69)))))) else (if i.val < 1336 then (if i.val < 1329 then (if i.val < 1326 then (if i.val < 1324 then (126, 227) else (if i.val < 1325 then (54, 178) else (82, 137))) else (if i.val < 1327 then (8, 3) else (if i.val < 1328 then (102, 7) else (34, 169)))) else (if i.val < 1332 then (if i.val < 1330 then (104, 110) else (if i.val < 1331 then (110, 46) else (31, 202))) else (if i.val < 1334 then (if i.val < 1333 then (103, 117) else (79, 207)) else (if i.val < 1335 then (85, 186) else (51, 173))))) else (if i.val < 1343 then (if i.val < 1339 then (if i.val < 1337 then (111, 36) else (if i.val < 1338 then (80, 151) else (28, 166))) else (if i.val < 1341 then (if i.val < 1340 then (111, 173) else (109, 221)) else (if i.val < 1342 then (31, 201) else (27, 173)))) else (if i.val < 1346 then (if i.val < 1344 then (118, 109) else (if i.val < 1345 then (109, 42) else (81, 132))) else (if i.val < 1348 then (if i.val < 1347 then (35, 217) else (91, 186)) else (if i.val < 1349 then (14, 97) else (9, 178))))))) else (if i.val < 1377 then (if i.val < 1363 then (if i.val < 1356 then (if i.val < 1353 then (if i.val < 1351 then (142, 14) else (if i.val < 1352 then (66, 36) else (122, 209))) else (if i.val < 1354 then (117, 65) else (if i.val < 1355 then (97, 181) else (49, 75)))) else (if i.val < 1359 then (if i.val < 1357 then (5, 192) else (if i.val < 1358 then (105, 215) else (77, 20))) else (if i.val < 1361 then (if i.val < 1360 then (113, 207) else (76, 135)) else (if i.val < 1362 then (119, 254) else (76, 16))))) else (if i.val < 1370 then (if i.val < 1366 then (if i.val < 1364 then (64, 64) else (if i.val < 1365 then (76, 144) else (94, 145))) else (if i.val < 1368 then (if i.val < 1367 then (106, 82) else (9, 205)) else (if i.val < 1369 then (65, 190) else (108, 139)))) else (if i.val < 1373 then (if i.val < 1371 then (130, 183) else (if i.val < 1372 then (63, 93) else (80, 131))) else (if i.val < 1375 then (if i.val < 1374 then (9, 97) else (65, 188)) else (if i.val < 1376 then (91, 14) else (107, 209)))))) else (if i.val < 1390 then (if i.val < 1383 then (if i.val < 1380 then (if i.val < 1378 then (132, 169) else (if i.val < 1379 then (101, 144) else (61, 202))) else (if i.val < 1381 then (127, 164) else (if i.val < 1382 then (78, 161) else (108, 234)))) else (if i.val < 1386 then (if i.val < 1384 then (78, 178) else (if i.val < 1385 then (107, 157) else (111, 56))) else (if i.val < 1388 then (if i.val < 1387 then (120, 18) else (59, 2)) else (if i.val < 1389 then (28, 13) else (52, 131))))) else (if i.val < 1397 then (if i.val < 1393 then (if i.val < 1391 then (120, 126) else (if i.val < 1392 then (97, 231) else (45, 228))) else (if i.val < 1395 then (if i.val < 1394 then (93, 120) else (34, 167)) else (if i.val < 1396 then (5, 137) else (120, 5)))) else (if i.val < 1400 then (if i.val < 1398 then (113, 100) else (if i.val < 1399 then (18, 200) else (93, 79))) else (if i.val < 1402 then (if i.val < 1401 then (136, 76) else (135, 24)) else (if i.val < 1403 then (83, 177) else (118, 225)))))))) else (if i.val < 1458 then (if i.val < 1431 then (if i.val < 1417 then (if i.val < 1410 then (if i.val < 1407 then (if i.val < 1405 then (87, 46) else (if i.val < 1406 then (20, 183) else (7, 85))) else (if i.val < 1408 then (7, 167) else (if i.val < 1409 then (39, 19) else (35, 113)))) else (if i.val < 1413 then (if i.val < 1411 then (19, 62) else (if i.val < 1412 then (122, 1) else (60, 227))) else (if i.val < 1415 then (if i.val < 1414 then (69, 141) else (78, 166)) else (if i.val < 1416 then (101, 248) else (80, 34))))) else (if i.val < 1424 then (if i.val < 1420 then (if i.val < 1418 then (6, 234) else (if i.val < 1419 then (60, 32) else (36, 157))) else (if i.val < 1422 then (if i.val < 1421 then (35, 119) else (38, 216)) else (if i.val < 1423 then (117, 96) else (59, 118)))) else (if i.val < 1427 then (if i.val < 1425 then (90, 63) else (if i.val < 1426 then (114, 35) else (85, 185))) else (if i.val < 1429 then (if i.val < 1428 then (129, 197) else (30, 130)) else (if i.val < 1430 then (136, 202) else (56, 252)))))) else (if i.val < 1444 then (if i.val < 1437 then (if i.val < 1434 then (if i.val < 1432 then (71, 236) else (if i.val < 1433 then (32, 43) else (15, 91))) else (if i.val < 1435 then (136, 237) else (if i.val < 1436 then (56, 204) else (32, 78)))) else (if i.val < 1440 then (if i.val < 1438 then (15, 0) else (if i.val < 1439 then (20, 187) else (57, 26))) else (if i.val < 1442 then (if i.val < 1441 then (86, 113) else (2, 15)) else (if i.val < 1443 then (93, 47) else (132, 247))))) else (if i.val < 1451 then (if i.val < 1447 then (if i.val < 1445 then (9, 93) else (if i.val < 1446 then (16, 11) else (90, 67))) else (if i.val < 1449 then (if i.val < 1448 then (90, 59) else (16, 12)) else (if i.val < 1450 then (25, 239) else (19, 252)))) else (if i.val < 1454 then (if i.val < 1452 then (36, 74) else (if i.val < 1453 then (119, 170) else (62, 19))) else (if i.val < 1456 then (if i.val < 1455 then (44, 42) else (127, 58)) else (if i.val < 1457 then (54, 46) else (112, 254))))))) else (if i.val < 1485 then (if i.val < 1471 then (if i.val < 1464 then (if i.val < 1461 then (if i.val < 1459 then (106, 171) else (if i.val < 1460 then (104, 54) else (64, 236))) else (if i.val < 1462 then (50, 159) else (if i.val < 1463 then (86, 213) else (60, 24)))) else (if i.val < 1467 then (if i.val < 1465 then (45, 84) else (if i.val < 1466 then (90, 253) else (94, 90))) else (if i.val < 1469 then (if i.val < 1468 then (38, 229) else (79, 54)) else (if i.val < 1470 then (88, 105) else (46, 41))))) else (if i.val < 1478 then (if i.val < 1474 then (if i.val < 1472 then (61, 101) else (if i.val < 1473 then (116, 37) else (39, 226))) else (if i.val < 1476 then (if i.val < 1475 then (20, 191) else (25, 172)) else (if i.val < 1477 then (129, 104) else (15, 118)))) else (if i.val < 1481 then (if i.val < 1479 then (16, 38) else (if i.val < 1480 then (17, 99) else (136, 22))) else (if i.val < 1483 then (if i.val < 1482 then (112, 211) else (28, 221)) else (if i.val < 1484 then (18, 250) else (64, 185)))))) else (if i.val < 1498 then (if i.val < 1491 then (if i.val < 1488 then (if i.val < 1486 then (1, 168) else (if i.val < 1487 then (75, 67) else (64, 94))) else (if i.val < 1489 then (135, 144) else (if i.val < 1490 then (19, 168) else (128, 152)))) else (if i.val < 1494 then (if i.val < 1492 then (141, 104) else (if i.val < 1493 then (66, 188) else (85, 197))) else (if i.val < 1496 then (if i.val < 1495 then (136, 197) else (28, 255)) else (if i.val < 1497 then (78, 135) else (103, 57))))) else (if i.val < 1505 then (if i.val < 1501 then (if i.val < 1499 then (113, 119) else (if i.val < 1500 then (47, 219) else (92, 150))) else (if i.val < 1503 then (if i.val < 1502 then (34, 198) else (85, 191)) else (if i.val < 1504 then (7, 63) else (38, 66)))) else (if i.val < 1508 then (if i.val < 1506 then (118, 62) else (if i.val < 1507 then (15, 61) else (51, 98))) else (if i.val < 1510 then (if i.val < 1509 then (120, 160) else (52, 88)) else (if i.val < 1511 then (22, 84) else (5, 27))))))))) else (if i.val < 1620 then (if i.val < 1566 then (if i.val < 1539 then (if i.val < 1525 then (if i.val < 1518 then (if i.val < 1515 then (if i.val < 1513 then (90, 154) else (if i.val < 1514 then (132, 69) else (10, 194))) else (if i.val < 1516 then (105, 15) else (if i.val < 1517 then (103, 28) else (89, 222)))) else (if i.val < 1521 then (if i.val < 1519 then (33, 115) else (if i.val < 1520 then (57, 97) else (89, 178))) else (if i.val < 1523 then (if i.val < 1522 then (93, 38) else (39, 84)) else (if i.val < 1524 then (116, 109) else (56, 172))))) else (if i.val < 1532 then (if i.val < 1528 then (if i.val < 1526 then (99, 4) else (if i.val < 1527 then (14, 138) else (30, 105))) else (if i.val < 1530 then (if i.val < 1529 then (14, 190) else (14, 11)) else (if i.val < 1531 then (75, 52) else (79, 102)))) else (if i.val < 1535 then (if i.val < 1533 then (116, 175) else (if i.val < 1534 then (112, 56) else (107, 241))) else (if i.val < 1537 then (if i.val < 1536 then (2, 190) else (32, 146)) else (if i.val < 1538 then (53, 181) else (82, 66)))))) else (if i.val < 1552 then (if i.val < 1545 then (if i.val < 1542 then (if i.val < 1540 then (90, 155) else (if i.val < 1541 then (107, 174) else (33, 121))) else (if i.val < 1543 then (5, 43) else (if i.val < 1544 then (67, 109) else (55, 54)))) else (if i.val < 1548 then (if i.val < 1546 then (30, 63) else (if i.val < 1547 then (131, 189) else (32, 180))) else (if i.val < 1550 then (if i.val < 1549 then (109, 52) else (113, 133)) else (if i.val < 1551 then (79, 97) else (5, 18))))) else (if i.val < 1559 then (if i.val < 1555 then (if i.val < 1553 then (44, 237) else (if i.val < 1554 then (142, 168) else (143, 61))) else (if i.val < 1557 then (if i.val < 1556 then (41, 194) else (74, 28)) else (if i.val < 1558 then (126, 23) else (85, 32)))) else (if i.val < 1562 then (if i.val < 1560 then (57, 98) else (if i.val < 1561 then (127, 163) else (134, 150))) else (if i.val < 1564 then (if i.val < 1563 then (109, 203) else (13, 187)) else (if i.val < 1565 then (67, 123) else (53, 188))))))) else (if i.val < 1593 then (if i.val < 1579 then (if i.val < 1572 then (if i.val < 1569 then (if i.val < 1567 then (117, 8) else (if i.val < 1568 then (113, 18) else (82, 109))) else (if i.val < 1570 then (33, 73) else (if i.val < 1571 then (115, 127) else (108, 202)))) else (if i.val < 1575 then (if i.val < 1573 then (16, 106) else (if i.val < 1574 then (95, 228) else (19, 95))) else (if i.val < 1577 then (if i.val < 1576 then (61, 99) else (39, 88)) else (if i.val < 1578 then (14, 184) else (52, 229))))) else (if i.val < 1586 then (if i.val < 1582 then (if i.val < 1580 then (47, 73) else (if i.val < 1581 then (118, 95) else (74, 137))) else (if i.val < 1584 then (if i.val < 1583 then (26, 182) else (41, 94)) else (if i.val < 1585 then (24, 192) else (27, 122)))) else (if i.val < 1589 then (if i.val < 1587 then (48, 65) else (if i.val < 1588 then (72, 146) else (52, 163))) else (if i.val < 1591 then (if i.val < 1590 then (26, 128) else (7, 212)) else (if i.val < 1592 then (12, 243) else (83, 27)))))) else (if i.val < 1606 then (if i.val < 1599 then (if i.val < 1596 then (if i.val < 1594 then (86, 69) else (if i.val < 1595 then (113, 130) else (47, 85))) else (if i.val < 1597 then (13, 5) else (if i.val < 1598 then (75, 123) else (78, 208)))) else (if i.val < 1602 then (if i.val < 1600 then (66, 150) else (if i.val < 1601 then (112, 169) else (98, 157))) else (if i.val < 1604 then (if i.val < 1603 then (117, 140) else (109, 34)) else (if i.val < 1605 then (105, 48) else (86, 166))))) else (if i.val < 1613 then (if i.val < 1609 then (if i.val < 1607 then (74, 26) else (if i.val < 1608 then (19, 248) else (62, 92))) else (if i.val < 1611 then (if i.val < 1610 then (23, 173) else (73, 95)) else (if i.val < 1612 then (51, 138) else (64, 246)))) else (if i.val < 1616 then (if i.val < 1614 then (120, 209) else (if i.val < 1615 then (107, 123) else (25, 115))) else (if i.val < 1618 then (if i.val < 1617 then (58, 199) else (45, 139)) else (if i.val < 1619 then (96, 131) else (100, 195)))))))) else (if i.val < 1674 then (if i.val < 1647 then (if i.val < 1633 then (if i.val < 1626 then (if i.val < 1623 then (if i.val < 1621 then (89, 208) else (if i.val < 1622 then (136, 124) else (11, 216))) else (if i.val < 1624 then (60, 175) else (if i.val < 1625 then (91, 46) else (123, 165)))) else (if i.val < 1629 then (if i.val < 1627 then (52, 116) else (if i.val < 1628 then (24, 131) else (47, 130))) else (if i.val < 1631 then (if i.val < 1630 then (29, 21) else (72, 94)) else (if i.val < 1632 then (88, 191) else (25, 0))))) else (if i.val < 1640 then (if i.val < 1636 then (if i.val < 1634 then (127, 177) else (if i.val < 1635 then (74, 141) else (131, 230))) else (if i.val < 1638 then (if i.val < 1637 then (10, 36) else (101, 254)) else (if i.val < 1639 then (84, 37) else (110, 131)))) else (if i.val < 1643 then (if i.val < 1641 then (56, 166) else (if i.val < 1642 then (58, 93) else (121, 178))) else (if i.val < 1645 then (if i.val < 1644 then (126, 134) else (98, 12)) else (if i.val < 1646 then (93, 175) else (43, 53)))))) else (if i.val < 1660 then (if i.val < 1653 then (if i.val < 1650 then (if i.val < 1648 then (89, 250) else (if i.val < 1649 then (112, 94) else (56, 224))) else (if i.val < 1651 then (104, 116) else (if i.val < 1652 then (89, 29) else (81, 44)))) else (if i.val < 1656 then (if i.val < 1654 then (12, 210) else (if i.val < 1655 then (27, 15) else (69, 252))) else (if i.val < 1658 then (if i.val < 1657 then (89, 56) else (11, 55)) else (if i.val < 1659 then (12, 179) else (24, 84))))) else (if i.val < 1667 then (if i.val < 1663 then (if i.val < 1661 then (41, 198) else (if i.val < 1662 then (12, 4) else (26, 179))) else (if i.val < 1665 then (if i.val < 1664 then (71, 105) else (95, 165)) else (if i.val < 1666 then (33, 39) else (114, 246)))) else (if i.val < 1670 then (if i.val < 1668 then (2, 218) else (if i.val < 1669 then (11, 242) else (4, 247))) else (if i.val < 1672 then (if i.val < 1671 then (87, 38) else (78, 63)) else (if i.val < 1673 then (87, 0) else (126, 75))))))) else (if i.val < 1701 then (if i.val < 1687 then (if i.val < 1680 then (if i.val < 1677 then (if i.val < 1675 then (6, 11) else (if i.val < 1676 then (88, 142) else (6, 5))) else (if i.val < 1678 then (77, 243) else (if i.val < 1679 then (20, 212) else (79, 222)))) else (if i.val < 1683 then (if i.val < 1681 then (25, 44) else (if i.val < 1682 then (115, 228) else (50, 186))) else (if i.val < 1685 then (if i.val < 1684 then (102, 138) else (77, 189)) else (if i.val < 1686 then (4, 67) else (114, 119))))) else (if i.val < 1694 then (if i.val < 1690 then (if i.val < 1688 then (57, 38) else (if i.val < 1689 then (68, 20) else (72, 32))) else (if i.val < 1692 then (if i.val < 1691 then (140, 33) else (137, 191)) else (if i.val < 1693 then (126, 185) else (90, 3)))) else (if i.val < 1697 then (if i.val < 1695 then (111, 185) else (if i.val < 1696 then (69, 162) else (105, 23))) else (if i.val < 1699 then (if i.val < 1698 then (62, 34) else (13, 123)) else (if i.val < 1700 then (37, 156) else (115, 102)))))) else (if i.val < 1714 then (if i.val < 1707 then (if i.val < 1704 then (if i.val < 1702 then (5, 33) else (if i.val < 1703 then (32, 72) else (14, 235))) else (if i.val < 1705 then (33, 53) else (if i.val < 1706 then (104, 88) else (64, 193)))) else (if i.val < 1710 then (if i.val < 1708 then (32, 131) else (if i.val < 1709 then (43, 68) else (36, 145))) else (if i.val < 1712 then (if i.val < 1711 then (40, 125) else (39, 93)) else (if i.val < 1713 then (33, 175) else (126, 131))))) else (if i.val < 1721 then (if i.val < 1717 then (if i.val < 1715 then (58, 62) else (if i.val < 1716 then (4, 225) else (13, 141))) else (if i.val < 1719 then (if i.val < 1718 then (114, 109) else (65, 139)) else (if i.val < 1720 then (41, 60) else (16, 235)))) else (if i.val < 1724 then (if i.val < 1722 then (81, 195) else (if i.val < 1723 then (47, 102) else (141, 160))) else (if i.val < 1726 then (if i.val < 1725 then (122, 246) else (98, 137)) else (if i.val < 1727 then (60, 119) else (108, 194))))))))))))

def g32p_supplierGroup02_classify : Fin 1728 → Fin 102 :=
  fun i => (if i.val < 864 then (if i.val < 432 then (if i.val < 216 then (if i.val < 108 then (if i.val < 54 then (if i.val < 27 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 34 else 11)) else (if i.val < 4 then 35 else (if i.val < 5 then 97 else 78))) else (if i.val < 9 then (if i.val < 7 then 86 else (if i.val < 8 then 78 else 4)) else (if i.val < 11 then (if i.val < 10 then 67 else 86) else (if i.val < 12 then 45 else 69)))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then 92 else (if i.val < 15 then 75 else 92)) else (if i.val < 18 then (if i.val < 17 then 56 else 63) else (if i.val < 19 then 75 else 40))) else (if i.val < 23 then (if i.val < 21 then 56 else (if i.val < 22 then 63 else 56)) else (if i.val < 25 then (if i.val < 24 then 1 else 63) else (if i.val < 26 then 2 else 63))))) else (if i.val < 40 then (if i.val < 33 then (if i.val < 30 then (if i.val < 28 then 40 else (if i.val < 29 then 40 else 101)) else (if i.val < 31 then 56 else (if i.val < 32 then 66 else 56))) else (if i.val < 36 then (if i.val < 34 then 24 else (if i.val < 35 then 28 else 66)) else (if i.val < 38 then (if i.val < 37 then 32 else 78) else (if i.val < 39 then 55 else 24)))) else (if i.val < 47 then (if i.val < 43 then (if i.val < 41 then 20 else (if i.val < 42 then 28 else 27)) else (if i.val < 45 then (if i.val < 44 then 55 else 35) else (if i.val < 46 then 32 else 78))) else (if i.val < 50 then (if i.val < 48 then 34 else (if i.val < 49 then 20 else 55)) else (if i.val < 52 then (if i.val < 51 then 27 else 34) else (if i.val < 53 then 20 else 20)))))) else (if i.val < 81 then (if i.val < 67 then (if i.val < 60 then (if i.val < 57 then (if i.val < 55 then 76 else (if i.val < 56 then 20 else 27)) else (if i.val < 58 then 27 else (if i.val < 59 then 55 else 20))) else (if i.val < 63 then (if i.val < 61 then 27 else (if i.val < 62 then 35 else 34)) else (if i.val < 65 then (if i.val < 64 then 27 else 34) else (if i.val < 66 then 13 else 78)))) else (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then 45 else (if i.val < 69 then 78 else 4)) else (if i.val < 72 then (if i.val < 71 then 7 else 45) else (if i.val < 73 then 10 else 4))) else (if i.val < 77 then (if i.val < 75 then 7 else (if i.val < 76 then 4 else 88)) else (if i.val < 79 then (if i.val < 78 then 7 else 95) else (if i.val < 80 then 7 else 10))))) else (if i.val < 94 then (if i.val < 87 then (if i.val < 84 then (if i.val < 82 then 10 else (if i.val < 83 then 13 else 17)) else (if i.val < 85 then 7 else (if i.val < 86 then 7 else 13))) else (if i.val < 90 then (if i.val < 88 then 61 else (if i.val < 89 then 88 else 61)) else (if i.val < 92 then (if i.val < 91 then 17 else 72) else (if i.val < 93 then 95 else 7)))) else (if i.val < 101 then (if i.val < 97 then (if i.val < 95 then 61 else (if i.val < 96 then 72 else 10)) else (if i.val < 99 then (if i.val < 98 then 13 else 7) else (if i.val < 100 then 13 else 13))) else (if i.val < 104 then (if i.val < 102 then 17 else (if i.val < 103 then 13 else 86)) else (if i.val < 106 then (if i.val < 105 then 17 else 61) else (if i.val < 107 then 61 else 72))))))) else (if i.val < 162 then (if i.val < 135 then (if i.val < 121 then (if i.val < 114 then (if i.val < 111 then (if i.val < 109 then 7 else (if i.val < 110 then 13 else 86)) else (if i.val < 112 then 61 else (if i.val < 113 then 61 else 86))) else (if i.val < 117 then (if i.val < 115 then 61 else (if i.val < 116 then 61 else 17)) else (if i.val < 119 then (if i.val < 118 then 86 else 61) else (if i.val < 120 then 72 else 78)))) else (if i.val < 128 then (if i.val < 124 then (if i.val < 122 then 61 else (if i.val < 123 then 78 else 17)) else (if i.val < 126 then (if i.val < 125 then 7 else 61) else (if i.val < 127 then 61 else 72))) else (if i.val < 131 then (if i.val < 129 then 78 else (if i.val < 130 then 72 else 13)) else (if i.val < 133 then (if i.val < 132 then 13 else 7) else (if i.val < 134 then 61 else 78))))) else (if i.val < 148 then (if i.val < 141 then (if i.val < 138 then (if i.val < 136 then 13 else (if i.val < 137 then 86 else 99)) else (if i.val < 139 then 4 else (if i.val < 140 then 40 else 4))) else (if i.val < 144 then (if i.val < 142 then 11 else (if i.val < 143 then 2 else 40)) else (if i.val < 146 then (if i.val < 145 then 6 else 63) else (if i.val < 147 then 11 else 80)))) else (if i.val < 155 then (if i.val < 151 then (if i.val < 149 then 2 else (if i.val < 150 then 58 else 63)) else (if i.val < 153 then (if i.val < 152 then 75 else 6) else (if i.val < 154 then 69 else 80))) else (if i.val < 158 then (if i.val < 156 then 63 else (if i.val < 157 then 58 else 69)) else (if i.val < 160 then (if i.val < 159 then 80 else 80) else (if i.val < 161 then 98 else 80)))))) else (if i.val < 189 then (if i.val < 175 then (if i.val < 168 then (if i.val < 165 then (if i.val < 163 then 58 else (if i.val < 164 then 58 else 63)) else (if i.val < 166 then 80 else (if i.val < 167 then 58 else 75))) else (if i.val < 171 then (if i.val < 169 then 69 else (if i.val < 170 then 58 else 69)) else (if i.val < 173 then (if i.val < 172 then 69 else 71) else (if i.val < 174 then 80 else 80)))) else (if i.val < 182 then (if i.val < 178 then (if i.val < 176 then 1 else (if i.val < 177 then 3 else 58)) else (if i.val < 180 then (if i.val < 179 then 69 else 40) else (if i.val < 181 then 80 else 48))) else (if i.val < 185 then (if i.val < 183 then 71 else (if i.val < 184 then 80 else 98)) else (if i.val < 187 then (if i.val < 186 then 80 else 40) else (if i.val < 188 then 81 else 58))))) else (if i.val < 202 then (if i.val < 195 then (if i.val < 192 then (if i.val < 190 then 59 else (if i.val < 191 then 80 else 59)) else (if i.val < 193 then 1 else (if i.val < 194 then 3 else 80))) else (if i.val < 198 then (if i.val < 196 then 80 else (if i.val < 197 then 58 else 59)) else (if i.val < 200 then (if i.val < 199 then 3 else 18) else (if i.val < 201 then 69 else 58)))) else (if i.val < 209 then (if i.val < 205 then (if i.val < 203 then 48 else (if i.val < 204 then 59 else 69)) else (if i.val < 207 then (if i.val < 206 then 6 else 92) else (if i.val < 208 then 71 else 80))) else (if i.val < 212 then (if i.val < 210 then 4 else (if i.val < 211 then 40 else 71)) else (if i.val < 214 then (if i.val < 213 then 40 else 40) else (if i.val < 215 then 81 else 80)))))))) else (if i.val < 324 then (if i.val < 270 then (if i.val < 243 then (if i.val < 229 then (if i.val < 222 then (if i.val < 219 then (if i.val < 217 then 1 else (if i.val < 218 then 75 else 80)) else (if i.val < 220 then 59 else (if i.val < 221 then 48 else 59))) else (if i.val < 225 then (if i.val < 223 then 92 else (if i.val < 224 then 71 else 40)) else (if i.val < 227 then (if i.val < 226 then 40 else 75) else (if i.val < 228 then 80 else 48)))) else (if i.val < 236 then (if i.val < 232 then (if i.val < 230 then 71 else (if i.val < 231 then 40 else 80)) else (if i.val < 234 then (if i.val < 233 then 56 else 40) else (if i.val < 235 then 56 else 71))) else (if i.val < 239 then (if i.val < 237 then 80 else (if i.val < 238 then 40 else 40)) else (if i.val < 241 then (if i.val < 240 then 81 else 56) else (if i.val < 242 then 80 else 59))))) else (if i.val < 256 then (if i.val < 249 then (if i.val < 246 then (if i.val < 244 then 59 else (if i.val < 245 then 80 else 40)) else (if i.val < 247 then 56 else (if i.val < 248 then 59 else 63))) else (if i.val < 252 then (if i.val < 250 then 71 else (if i.val < 251 then 80 else 3)) else (if i.val < 254 then (if i.val < 253 then 92 else 40) else (if i.val < 255 then 48 else 80)))) else (if i.val < 263 then (if i.val < 259 then (if i.val < 257 then 56 else (if i.val < 258 then 59 else 59)) else (if i.val < 261 then (if i.val < 260 then 80 else 59) else (if i.val < 262 then 75 else 59))) else (if i.val < 266 then (if i.val < 264 then 6 else (if i.val < 265 then 80 else 92)) else (if i.val < 268 then (if i.val < 267 then 48 else 56) else (if i.val < 269 then 59 else 63)))))) else (if i.val < 297 then (if i.val < 283 then (if i.val < 276 then (if i.val < 273 then (if i.val < 271 then 59 else (if i.val < 272 then 75 else 6)) else (if i.val < 274 then 34 else (if i.val < 275 then 56 else 32))) else (if i.val < 279 then (if i.val < 277 then 56 else (if i.val < 278 then 24 else 27)) else (if i.val < 281 then (if i.val < 280 then 32 else 15) else (if i.val < 282 then 27 else 24)))) else (if i.val < 290 then (if i.val < 286 then (if i.val < 284 then 76 else (if i.val < 285 then 27 else 100)) else (if i.val < 288 then (if i.val < 287 then 27 else 15) else (if i.val < 289 then 15 else 27))) else (if i.val < 293 then (if i.val < 291 then 27 else (if i.val < 292 then 34 else 41)) else (if i.val < 295 then (if i.val < 294 then 76 else 41) else (if i.val < 296 then 20 else 55))))) else (if i.val < 310 then (if i.val < 303 then (if i.val < 300 then (if i.val < 298 then 100 else (if i.val < 299 then 27 else 41)) else (if i.val < 301 then 55 else (if i.val < 302 then 15 else 34))) else (if i.val < 306 then (if i.val < 304 then 27 else (if i.val < 305 then 34 else 34)) else (if i.val < 308 then (if i.val < 307 then 66 else 20) else (if i.val < 309 then 41 else 41)))) else (if i.val < 317 then (if i.val < 313 then (if i.val < 311 then 55 else (if i.val < 312 then 27 else 66)) else (if i.val < 315 then (if i.val < 314 then 41 else 41) else (if i.val < 316 then 66 else 41))) else (if i.val < 320 then (if i.val < 318 then 41 else (if i.val < 319 then 66 else 41)) else (if i.val < 322 then (if i.val < 321 then 55 else 56) else (if i.val < 323 then 41 else 56))))))) else (if i.val < 378 then (if i.val < 351 then (if i.val < 337 then (if i.val < 330 then (if i.val < 327 then (if i.val < 325 then 27 else (if i.val < 326 then 41 else 41)) else (if i.val < 328 then 55 else (if i.val < 329 then 56 else 55))) else (if i.val < 333 then (if i.val < 331 then 34 else (if i.val < 332 then 34 else 27)) else (if i.val < 335 then (if i.val < 334 then 41 else 56) else (if i.val < 336 then 34 else 66)))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then 11 else (if i.val < 339 then 15 else 66)) else (if i.val < 342 then (if i.val < 341 then 66 else 35) else (if i.val < 343 then 20 else 41))) else (if i.val < 347 then (if i.val < 345 then 41 else (if i.val < 346 then 15 else 20)) else (if i.val < 349 then (if i.val < 348 then 11 else 76) else (if i.val < 350 then 11 else 11))))) else (if i.val < 364 then (if i.val < 357 then (if i.val < 354 then (if i.val < 352 then 15 else (if i.val < 353 then 66 else 15)) else (if i.val < 355 then 15 else (if i.val < 356 then 19 else 41))) else (if i.val < 360 then (if i.val < 358 then 66 else (if i.val < 359 then 32 else 41)) else (if i.val < 362 then (if i.val < 361 then 43 else 66) else (if i.val < 363 then 43 else 35)))) else (if i.val < 371 then (if i.val < 367 then (if i.val < 365 then 20 else (if i.val < 366 then 66 else 32)) else (if i.val < 369 then (if i.val < 368 then 41 else 24) else (if i.val < 370 then 20 else 25))) else (if i.val < 374 then (if i.val < 372 then 56 else (if i.val < 373 then 41 else 15)) else (if i.val < 376 then (if i.val < 375 then 24 else 56) else (if i.val < 377 then 27 else 15)))))) else (if i.val < 405 then (if i.val < 391 then (if i.val < 384 then (if i.val < 381 then (if i.val < 379 then 20 else (if i.val < 380 then 27 else 11)) else (if i.val < 382 then 15 else (if i.val < 383 then 19 else 41))) else (if i.val < 387 then (if i.val < 385 then 43 else (if i.val < 386 then 25 else 56)) else (if i.val < 389 then (if i.val < 388 then 19 else 25) else (if i.val < 390 then 15 else 11)))) else (if i.val < 398 then (if i.val < 394 then (if i.val < 392 then 15 else (if i.val < 393 then 76 else 11)) else (if i.val < 396 then (if i.val < 395 then 41 else 43) else (if i.val < 397 then 56 else 27))) else (if i.val < 401 then (if i.val < 399 then 11 else (if i.val < 400 then 15 else 66)) else (if i.val < 403 then (if i.val < 402 then 55 else 66) else (if i.val < 404 then 11 else 27))))) else (if i.val < 418 then (if i.val < 411 then (if i.val < 408 then (if i.val < 406 then 15 else (if i.val < 407 then 15 else 27)) else (if i.val < 409 then 32 else (if i.val < 410 then 66 else 35))) else (if i.val < 414 then (if i.val < 412 then 28 else (if i.val < 413 then 32 else 20)) else (if i.val < 416 then (if i.val < 415 then 24 else 15) else (if i.val < 417 then 24 else 15)))) else (if i.val < 425 then (if i.val < 421 then (if i.val < 419 then 20 else (if i.val < 420 then 35 else 43)) else (if i.val < 423 then (if i.val < 422 then 11 else 76) else (if i.val < 424 then 32 else 43))) else (if i.val < 428 then (if i.val < 426 then 11 else (if i.val < 427 then 27 else 78)) else (if i.val < 430 then (if i.val < 429 then 55 else 66) else (if i.val < 431 then 28 else 32))))))))) else (if i.val < 648 then (if i.val < 540 then (if i.val < 486 then (if i.val < 459 then (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then 15 else (if i.val < 434 then 55 else 35)) else (if i.val < 436 then 43 else (if i.val < 437 then 32 else 43))) else (if i.val < 441 then (if i.val < 439 then 55 else (if i.val < 440 then 66 else 34)) else (if i.val < 443 then (if i.val < 442 then 35 else 43) else (if i.val < 444 then 43 else 66)))) else (if i.val < 452 then (if i.val < 448 then (if i.val < 446 then 34 else (if i.val < 447 then 43 else 20)) else (if i.val < 450 then (if i.val < 449 then 55 else 66) else (if i.val < 451 then 78 else 27))) else (if i.val < 455 then (if i.val < 453 then 15 else (if i.val < 454 then 34 else 24)) else (if i.val < 457 then (if i.val < 456 then 35 else 43) else (if i.val < 458 then 55 else 43))))) else (if i.val < 472 then (if i.val < 465 then (if i.val < 462 then (if i.val < 460 then 27 else (if i.val < 461 then 66 else 78)) else (if i.val < 463 then 15 else (if i.val < 464 then 34 else 20))) else (if i.val < 468 then (if i.val < 466 then 43 else (if i.val < 467 then 55 else 27)) else (if i.val < 470 then (if i.val < 469 then 15 else 66) else (if i.val < 471 then 78 else 11)))) else (if i.val < 479 then (if i.val < 475 then (if i.val < 473 then 15 else (if i.val < 474 then 15 else 19)) else (if i.val < 477 then (if i.val < 476 then 24 else 32) else (if i.val < 478 then 43 else 43))) else (if i.val < 482 then (if i.val < 480 then 25 else (if i.val < 481 then 24 else 27)) else (if i.val < 484 then (if i.val < 483 then 43 else 55) else (if i.val < 485 then 11 else 43)))))) else (if i.val < 513 then (if i.val < 499 then (if i.val < 492 then (if i.val < 489 then (if i.val < 487 then 27 else (if i.val < 488 then 15 else 32)) else (if i.val < 490 then 66 else (if i.val < 491 then 78 else 55))) else (if i.val < 495 then (if i.val < 493 then 15 else (if i.val < 494 then 24 else 43)) else (if i.val < 497 then (if i.val < 496 then 20 else 27) else (if i.val < 498 then 43 else 55)))) else (if i.val < 506 then (if i.val < 502 then (if i.val < 500 then 35 else (if i.val < 501 then 27 else 32)) else (if i.val < 504 then (if i.val < 503 then 96 else 24) else (if i.val < 505 then 10 else 24))) else (if i.val < 509 then (if i.val < 507 then 92 else (if i.val < 508 then 95 else 10)) else (if i.val < 511 then (if i.val < 510 then 84 else 7) else (if i.val < 512 then 92 else 61))))) else (if i.val < 526 then (if i.val < 519 then (if i.val < 516 then (if i.val < 514 then 95 else (if i.val < 515 then 72 else 7)) else (if i.val < 517 then 45 else (if i.val < 518 then 84 else 7))) else (if i.val < 522 then (if i.val < 520 then 72 else (if i.val < 521 then 61 else 61)) else (if i.val < 524 then (if i.val < 523 then 87 else 72) else (if i.val < 525 then 72 else 7)))) else (if i.val < 533 then (if i.val < 529 then (if i.val < 527 then 61 else (if i.val < 528 then 72 else 45)) else (if i.val < 531 then (if i.val < 530 then 13 else 72) else (if i.val < 532 then 13 else 88))) else (if i.val < 536 then (if i.val < 534 then 23 else (if i.val < 535 then 72 else 10)) else (if i.val < 538 then (if i.val < 537 then 61 else 17) else (if i.val < 539 then 86 else 61))))))) else (if i.val < 594 then (if i.val < 567 then (if i.val < 553 then (if i.val < 546 then (if i.val < 543 then (if i.val < 541 then 87 else (if i.val < 542 then 10 else 64)) else (if i.val < 544 then 72 else (if i.val < 545 then 74 else 61))) else (if i.val < 549 then (if i.val < 547 then 74 else (if i.val < 548 then 23 else 61)) else (if i.val < 551 then (if i.val < 550 then 61 else 72) else (if i.val < 552 then 74 else 23)))) else (if i.val < 560 then (if i.val < 556 then (if i.val < 554 then 82 else (if i.val < 555 then 13 else 72)) else (if i.val < 558 then (if i.val < 557 then 17 else 74) else (if i.val < 559 then 13 else 84))) else (if i.val < 563 then (if i.val < 561 then 24 else (if i.val < 562 then 10 else 86)) else (if i.val < 565 then (if i.val < 564 then 10 else 10) else (if i.val < 566 then 64 else 61))))) else (if i.val < 580 then (if i.val < 573 then (if i.val < 570 then (if i.val < 568 then 88 else (if i.val < 569 then 45 else 61)) else (if i.val < 571 then 74 else (if i.val < 572 then 17 else 74))) else (if i.val < 576 then (if i.val < 574 then 10 else (if i.val < 575 then 10 else 45)) else (if i.val < 578 then (if i.val < 577 then 61 else 17) else (if i.val < 579 then 10 else 61)))) else (if i.val < 587 then (if i.val < 583 then (if i.val < 581 then 4 else (if i.val < 582 then 10 else 4)) else (if i.val < 585 then (if i.val < 584 then 10 else 10) else (if i.val < 586 then 64 else 4))) else (if i.val < 590 then (if i.val < 588 then 61 else (if i.val < 589 then 74 else 74)) else (if i.val < 592 then (if i.val < 591 then 10 else 4) else (if i.val < 593 then 74 else 7)))))) else (if i.val < 621 then (if i.val < 607 then (if i.val < 600 then (if i.val < 597 then (if i.val < 595 then 23 else (if i.val < 596 then 78 else 10)) else (if i.val < 598 then 17 else (if i.val < 599 then 61 else 4))) else (if i.val < 603 then (if i.val < 601 then 74 else (if i.val < 602 then 74 else 61)) else (if i.val < 605 then (if i.val < 604 then 74 else 45) else (if i.val < 606 then 74 else 84)))) else (if i.val < 614 then (if i.val < 610 then (if i.val < 608 then 78 else (if i.val < 609 then 17 else 4)) else (if i.val < 612 then (if i.val < 611 then 74 else 7) else (if i.val < 613 then 74 else 45))) else (if i.val < 617 then (if i.val < 615 then 84 else (if i.val < 616 then 24 else 72)) else (if i.val < 619 then (if i.val < 618 then 10 else 86) else (if i.val < 620 then 67 else 45))))) else (if i.val < 634 then (if i.val < 627 then (if i.val < 624 then (if i.val < 622 then 10 else (if i.val < 623 then 10 else 72)) else (if i.val < 625 then 84 else (if i.val < 626 then 64 else 29))) else (if i.val < 630 then (if i.val < 628 then 45 else (if i.val < 629 then 29 else 86)) else (if i.val < 632 then (if i.val < 631 then 91 else 45) else (if i.val < 633 then 29 else 74)))) else (if i.val < 641 then (if i.val < 637 then (if i.val < 635 then 17 else (if i.val < 636 then 86 else 29)) else (if i.val < 639 then (if i.val < 638 then 74 else 79) else (if i.val < 640 then 92 else 72))) else (if i.val < 644 then (if i.val < 642 then 86 else (if i.val < 643 then 72 else 84)) else (if i.val < 646 then (if i.val < 645 then 10 else 95) else (if i.val < 647 then 84 else 92)))))))) else (if i.val < 756 then (if i.val < 702 then (if i.val < 675 then (if i.val < 661 then (if i.val < 654 then (if i.val < 651 then (if i.val < 649 then 86 else (if i.val < 650 then 92 else 67)) else (if i.val < 652 then 45 else (if i.val < 653 then 83 else 45))) else (if i.val < 657 then (if i.val < 655 then 29 else (if i.val < 656 then 4 else 10)) else (if i.val < 659 then (if i.val < 658 then 83 else 4) else (if i.val < 660 then 17 else 72)))) else (if i.val < 668 then (if i.val < 664 then (if i.val < 662 then 84 else (if i.val < 663 then 29 else 72)) else (if i.val < 666 then (if i.val < 665 then 84 else 83) else (if i.val < 667 then 29 else 84))) else (if i.val < 671 then (if i.val < 669 then 29 else (if i.val < 670 then 72 else 29)) else (if i.val < 673 then (if i.val < 672 then 72 else 45) else (if i.val < 674 then 29 else 10))))) else (if i.val < 688 then (if i.val < 681 then (if i.val < 678 then (if i.val < 676 then 83 else (if i.val < 677 then 91 else 29)) else (if i.val < 679 then 23 else (if i.val < 680 then 7 else 86))) else (if i.val < 684 then (if i.val < 682 then 45 else (if i.val < 683 then 29 else 74)) else (if i.val < 686 then (if i.val < 685 then 10 else 84) else (if i.val < 687 then 17 else 92)))) else (if i.val < 695 then (if i.val < 691 then (if i.val < 689 then 45 else (if i.val < 690 then 29 else 4)) else (if i.val < 693 then (if i.val < 692 then 74 else 29) else (if i.val < 694 then 23 else 29))) else (if i.val < 698 then (if i.val < 696 then 23 else (if i.val < 697 then 74 else 92)) else (if i.val < 700 then (if i.val < 699 then 72 else 84) else (if i.val < 701 then 86 else 86)))))) else (if i.val < 729 then (if i.val < 715 then (if i.val < 708 then (if i.val < 705 then (if i.val < 703 then 29 else (if i.val < 704 then 79 else 86)) else (if i.val < 706 then 92 else (if i.val < 707 then 4 else 17))) else (if i.val < 711 then (if i.val < 709 then 7 else (if i.val < 710 then 92 else 72)) else (if i.val < 713 then (if i.val < 712 then 86 else 79) else (if i.val < 714 then 86 else 7)))) else (if i.val < 722 then (if i.val < 718 then (if i.val < 716 then 92 else (if i.val < 717 then 72 else 72)) else (if i.val < 720 then (if i.val < 719 then 95 else 84) else (if i.val < 721 then 86 else 67))) else (if i.val < 725 then (if i.val < 723 then 45 else (if i.val < 724 then 83 else 72)) else (if i.val < 727 then (if i.val < 726 then 83 else 72) else (if i.val < 728 then 84 else 84))))) else (if i.val < 742 then (if i.val < 735 then (if i.val < 732 then (if i.val < 730 then 83 else (if i.val < 731 then 84 else 29)) else (if i.val < 733 then 29 else (if i.val < 734 then 45 else 95))) else (if i.val < 738 then (if i.val < 736 then 83 else (if i.val < 737 then 29 else 91)) else (if i.val < 740 then (if i.val < 739 then 7 else 45) else (if i.val < 741 then 91 else 29)))) else (if i.val < 749 then (if i.val < 745 then (if i.val < 743 then 45 else (if i.val < 744 then 13 else 92)) else (if i.val < 747 then (if i.val < 746 then 72 else 86) else (if i.val < 748 then 29 else 13))) else (if i.val < 752 then (if i.val < 750 then 17 else (if i.val < 751 then 92 else 72)) else (if i.val < 754 then (if i.val < 753 then 17 else 7) else (if i.val < 755 then 17 else 72))))))) else (if i.val < 810 then (if i.val < 783 then (if i.val < 769 then (if i.val < 762 then (if i.val < 759 then (if i.val < 757 then 84 else (if i.val < 758 then 83 else 95)) else (if i.val < 760 then 83 else (if i.val < 761 then 13 else 92))) else (if i.val < 765 then (if i.val < 763 then 7 else (if i.val < 764 then 13 else 92)) else (if i.val < 767 then (if i.val < 766 then 17 else 17) else (if i.val < 768 then 7 else 13)))) else (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then 13 else (if i.val < 771 then 61 else 13)) else (if i.val < 774 then (if i.val < 773 then 17 else 7) else (if i.val < 775 then 13 else 86))) else (if i.val < 779 then (if i.val < 777 then 13 else (if i.val < 778 then 61 else 17)) else (if i.val < 781 then (if i.val < 780 then 72 else 7) else (if i.val < 782 then 72 else 13))))) else (if i.val < 796 then (if i.val < 789 then (if i.val < 786 then (if i.val < 784 then 83 else (if i.val < 785 then 29 else 13)) else (if i.val < 787 then 61 else (if i.val < 788 then 13 else 17))) else (if i.val < 792 then (if i.val < 790 then 7 else (if i.val < 791 then 7 else 17)) else (if i.val < 794 then (if i.val < 793 then 72 else 13) else (if i.val < 795 then 83 else 86)))) else (if i.val < 803 then (if i.val < 799 then (if i.val < 797 then 91 else (if i.val < 798 then 13 else 61)) else (if i.val < 801 then (if i.val < 800 then 72 else 17) else (if i.val < 802 then 7 else 86))) else (if i.val < 806 then (if i.val < 804 then 13 else (if i.val < 805 then 29 else 86)) else (if i.val < 808 then (if i.val < 807 then 13 else 92) else (if i.val < 809 then 45 else 29)))))) else (if i.val < 837 then (if i.val < 823 then (if i.val < 816 then (if i.val < 813 then (if i.val < 811 then 17 else (if i.val < 812 then 29 else 72)) else (if i.val < 814 then 29 else (if i.val < 815 then 23 else 61))) else (if i.val < 819 then (if i.val < 817 then 79 else (if i.val < 818 then 92 else 17)) else (if i.val < 821 then (if i.val < 820 then 7 else 86) else (if i.val < 822 then 86 else 13)))) else (if i.val < 830 then (if i.val < 826 then (if i.val < 824 then 17 else (if i.val < 825 then 86 else 13)) else (if i.val < 828 then (if i.val < 827 then 61 else 17) else (if i.val < 829 then 61 else 72))) else (if i.val < 833 then (if i.val < 831 then 17 else (if i.val < 832 then 7 else 13)) else (if i.val < 835 then (if i.val < 834 then 69 else 4) else (if i.val < 836 then 6 else 11))))) else (if i.val < 850 then (if i.val < 843 then (if i.val < 840 then (if i.val < 838 then 58 else (if i.val < 839 then 71 else 58)) else (if i.val < 841 then 11 else (if i.val < 842 then 98 else 58))) else (if i.val < 846 then (if i.val < 844 then 93 else (if i.val < 845 then 58 else 71)) else (if i.val < 848 then (if i.val < 847 then 71 else 58) else (if i.val < 849 then 58 else 48)))) else (if i.val < 857 then (if i.val < 853 then (if i.val < 851 then 98 else (if i.val < 852 then 48 else 63)) else (if i.val < 855 then (if i.val < 854 then 93 else 58) else (if i.val < 856 then 48 else 63))) else (if i.val < 860 then (if i.val < 858 then 71 else (if i.val < 859 then 69 else 58)) else (if i.val < 862 then (if i.val < 861 then 69 else 48) else (if i.val < 863 then 63 else 58)))))))))) else (if i.val < 1296 then (if i.val < 1080 then (if i.val < 972 then (if i.val < 918 then (if i.val < 891 then (if i.val < 877 then (if i.val < 870 then (if i.val < 867 then (if i.val < 865 then 48 else (if i.val < 866 then 48 else 48)) else (if i.val < 868 then 48 else (if i.val < 869 then 63 else 4))) else (if i.val < 873 then (if i.val < 871 then 4 else (if i.val < 872 then 58 else 48)) else (if i.val < 875 then (if i.val < 874 then 48 else 63) else (if i.val < 876 then 4 else 63)))) else (if i.val < 884 then (if i.val < 880 then (if i.val < 878 then 69 else (if i.val < 879 then 69 else 58)) else (if i.val < 882 then (if i.val < 881 then 48 else 4) else (if i.val < 883 then 69 else 40))) else (if i.val < 887 then (if i.val < 885 then 48 else (if i.val < 886 then 71 else 92)) else (if i.val < 889 then (if i.val < 888 then 98 else 92) else (if i.val < 890 then 40 else 71))))) else (if i.val < 904 then (if i.val < 897 then (if i.val < 894 then (if i.val < 892 then 71 else (if i.val < 893 then 8 else 48)) else (if i.val < 895 then 6 else (if i.val < 896 then 48 else 50))) else (if i.val < 900 then (if i.val < 898 then 40 else (if i.val < 899 then 50 else 40)) else (if i.val < 902 then (if i.val < 901 then 6 else 48) else (if i.val < 903 then 11 else 59)))) else (if i.val < 911 then (if i.val < 907 then (if i.val < 905 then 4 else (if i.val < 906 then 71 else 11)) else (if i.val < 909 then (if i.val < 908 then 4 else 58) else (if i.val < 910 then 58 else 92))) else (if i.val < 914 then (if i.val < 912 then 71 else (if i.val < 913 then 8 else 48)) else (if i.val < 916 then (if i.val < 915 then 50 else 59) else (if i.val < 917 then 4 else 8)))))) else (if i.val < 945 then (if i.val < 931 then (if i.val < 924 then (if i.val < 921 then (if i.val < 919 then 59 else (if i.val < 920 then 71 else 92)) else (if i.val < 922 then 92 else (if i.val < 923 then 48 else 50))) else (if i.val < 927 then (if i.val < 925 then 4 else (if i.val < 926 then 58 else 92)) else (if i.val < 929 then (if i.val < 928 then 71 else 40) else (if i.val < 930 then 58 else 71)))) else (if i.val < 938 then (if i.val < 934 then (if i.val < 932 then 71 else (if i.val < 933 then 58 else 6)) else (if i.val < 936 then (if i.val < 935 then 40 else 2) else (if i.val < 937 then 6 else 11))) else (if i.val < 941 then (if i.val < 939 then 71 else (if i.val < 940 then 11 else 80)) else (if i.val < 943 then (if i.val < 942 then 75 else 50) else (if i.val < 944 then 92 else 98))))) else (if i.val < 958 then (if i.val < 951 then (if i.val < 948 then (if i.val < 946 then 6 else (if i.val < 947 then 50 else 92)) else (if i.val < 949 then 58 else (if i.val < 950 then 2 else 6))) else (if i.val < 954 then (if i.val < 952 then 71 else (if i.val < 953 then 63 else 75)) else (if i.val < 956 then (if i.val < 955 then 50 else 6) else (if i.val < 957 then 50 else 69)))) else (if i.val < 965 then (if i.val < 961 then (if i.val < 959 then 75 else (if i.val < 960 then 50 else 50)) else (if i.val < 963 then (if i.val < 962 then 69 else 50) else (if i.val < 964 then 80 else 58))) else (if i.val < 968 then (if i.val < 966 then 71 else (if i.val < 967 then 69 else 11)) else (if i.val < 970 then (if i.val < 969 then 75 else 50) else (if i.val < 971 then 63 else 50))))))) else (if i.val < 1026 then (if i.val < 999 then (if i.val < 985 then (if i.val < 978 then (if i.val < 975 then (if i.val < 973 then 58 else (if i.val < 974 then 71 else 69)) else (if i.val < 976 then 80 else (if i.val < 977 then 50 else 63))) else (if i.val < 981 then (if i.val < 979 then 58 else (if i.val < 980 then 92 else 71)) else (if i.val < 983 then (if i.val < 982 then 8 else 11) else (if i.val < 984 then 6 else 50)))) else (if i.val < 992 then (if i.val < 988 then (if i.val < 986 then 50 else (if i.val < 987 then 59 else 11)) else (if i.val < 990 then (if i.val < 989 then 58 else 50) else (if i.val < 991 then 63 else 92))) else (if i.val < 995 then (if i.val < 993 then 50 else (if i.val < 994 then 58 else 6)) else (if i.val < 997 then (if i.val < 996 then 63 else 71) else (if i.val < 998 then 11 else 50))))) else (if i.val < 1012 then (if i.val < 1005 then (if i.val < 1002 then (if i.val < 1000 then 80 else (if i.val < 1001 then 58 else 50)) else (if i.val < 1003 then 63 else (if i.val < 1004 then 75 else 58))) else (if i.val < 1008 then (if i.val < 1006 then 6 else (if i.val < 1007 then 56 else 93)) else (if i.val < 1010 then (if i.val < 1009 then 63 else 63) else (if i.val < 1011 then 75 else 71)))) else (if i.val < 1019 then (if i.val < 1015 then (if i.val < 1013 then 58 else (if i.val < 1014 then 6 else 5)) else (if i.val < 1017 then (if i.val < 1016 then 2 else 5) else (if i.val < 1018 then 63 else 75))) else (if i.val < 1022 then (if i.val < 1020 then 6 else (if i.val < 1021 then 69 else 40)) else (if i.val < 1024 then (if i.val < 1023 then 50 else 11) else (if i.val < 1025 then 71 else 63)))))) else (if i.val < 1053 then (if i.val < 1039 then (if i.val < 1032 then (if i.val < 1029 then (if i.val < 1027 then 69 else (if i.val < 1028 then 11 else 48)) else (if i.val < 1030 then 93 else (if i.val < 1031 then 75 else 80))) else (if i.val < 1035 then (if i.val < 1033 then 56 else (if i.val < 1034 then 75 else 5)) else (if i.val < 1037 then (if i.val < 1036 then 56 else 93) else (if i.val < 1038 then 40 else 56)))) else (if i.val < 1046 then (if i.val < 1042 then (if i.val < 1040 then 5 else (if i.val < 1041 then 48 else 56)) else (if i.val < 1044 then (if i.val < 1043 then 63 else 48) else (if i.val < 1045 then 63 else 98))) else (if i.val < 1049 then (if i.val < 1047 then 89 else (if i.val < 1048 then 6 else 94)) else (if i.val < 1051 then (if i.val < 1050 then 63 else 94) else (if i.val < 1052 then 94 else 50))))) else (if i.val < 1066 then (if i.val < 1059 then (if i.val < 1056 then (if i.val < 1054 then 93 else (if i.val < 1055 then 94 else 50)) else (if i.val < 1057 then 81 else (if i.val < 1058 then 48 else 58))) else (if i.val < 1062 then (if i.val < 1060 then 5 else (if i.val < 1061 then 69 else 48)) else (if i.val < 1064 then (if i.val < 1063 then 5 else 48) else (if i.val < 1065 then 2 else 5)))) else (if i.val < 1073 then (if i.val < 1069 then (if i.val < 1067 then 75 else (if i.val < 1068 then 5 else 8)) else (if i.val < 1071 then (if i.val < 1070 then 80 else 63) else (if i.val < 1072 then 58 else 89))) else (if i.val < 1076 then (if i.val < 1074 then 94 else (if i.val < 1075 then 69 else 11)) else (if i.val < 1078 then (if i.val < 1077 then 69 else 80) else (if i.val < 1079 then 94 else 98)))))))) else (if i.val < 1188 then (if i.val < 1134 then (if i.val < 1107 then (if i.val < 1093 then (if i.val < 1086 then (if i.val < 1083 then (if i.val < 1081 then 89 else (if i.val < 1082 then 63 else 48)) else (if i.val < 1084 then 63 else (if i.val < 1085 then 94 else 69))) else (if i.val < 1089 then (if i.val < 1087 then 75 else (if i.val < 1088 then 80 else 94)) else (if i.val < 1091 then (if i.val < 1090 then 80 else 63) else (if i.val < 1092 then 48 else 63)))) else (if i.val < 1100 then (if i.val < 1096 then (if i.val < 1094 then 75 else (if i.val < 1095 then 5 else 56)) else (if i.val < 1098 then (if i.val < 1097 then 75 else 94) else (if i.val < 1099 then 50 else 6))) else (if i.val < 1103 then (if i.val < 1101 then 50 else (if i.val < 1102 then 8 else 56)) else (if i.val < 1105 then (if i.val < 1104 then 63 else 11) else (if i.val < 1106 then 58 else 8))))) else (if i.val < 1120 then (if i.val < 1113 then (if i.val < 1110 then (if i.val < 1108 then 63 else (if i.val < 1109 then 50 else 48)) else (if i.val < 1111 then 63 else (if i.val < 1112 then 75 else 40))) else (if i.val < 1116 then (if i.val < 1114 then 5 else (if i.val < 1115 then 48 else 71)) else (if i.val < 1118 then (if i.val < 1117 then 94 else 81) else (if i.val < 1119 then 80 else 48)))) else (if i.val < 1127 then (if i.val < 1123 then (if i.val < 1121 then 63 else (if i.val < 1122 then 81 else 89)) else (if i.val < 1125 then (if i.val < 1124 then 18 else 48) else (if i.val < 1126 then 63 else 80))) else (if i.val < 1130 then (if i.val < 1128 then 63 else (if i.val < 1129 then 94 else 93)) else (if i.val < 1132 then (if i.val < 1131 then 94 else 58) else (if i.val < 1133 then 69 else 2)))))) else (if i.val < 1161 then (if i.val < 1147 then (if i.val < 1140 then (if i.val < 1137 then (if i.val < 1135 then 75 else (if i.val < 1136 then 80 else 58)) else (if i.val < 1138 then 69 else (if i.val < 1139 then 58 else 69))) else (if i.val < 1143 then (if i.val < 1141 then 80 else (if i.val < 1142 then 63 else 69)) else (if i.val < 1145 then (if i.val < 1144 then 59 else 75) else (if i.val < 1146 then 80 else 48)))) else (if i.val < 1154 then (if i.val < 1150 then (if i.val < 1148 then 93 else (if i.val < 1149 then 5 else 63)) else (if i.val < 1152 then (if i.val < 1151 then 69 else 69) else (if i.val < 1153 then 63 else 58))) else (if i.val < 1157 then (if i.val < 1155 then 5 else (if i.val < 1156 then 48 else 6)) else (if i.val < 1159 then (if i.val < 1158 then 69 else 48) else (if i.val < 1160 then 63 else 80))))) else (if i.val < 1174 then (if i.val < 1167 then (if i.val < 1164 then (if i.val < 1162 then 58 else (if i.val < 1163 then 69 else 80)) else (if i.val < 1165 then 75 else (if i.val < 1166 then 69 else 48))) else (if i.val < 1170 then (if i.val < 1168 then 59 else (if i.val < 1169 then 6 else 69)) else (if i.val < 1172 then (if i.val < 1171 then 48 else 75) else (if i.val < 1173 then 59 else 6)))) else (if i.val < 1181 then (if i.val < 1177 then (if i.val < 1175 then 48 else (if i.val < 1176 then 80 else 71)) else (if i.val < 1179 then (if i.val < 1178 then 75 else 80) else (if i.val < 1180 then 6 else 48))) else (if i.val < 1184 then (if i.val < 1182 then 63 else (if i.val < 1183 then 4 else 75)) else (if i.val < 1186 then (if i.val < 1185 then 80 else 75) else (if i.val < 1187 then 6 else 63))))))) else (if i.val < 1242 then (if i.val < 1215 then (if i.val < 1201 then (if i.val < 1194 then (if i.val < 1191 then (if i.val < 1189 then 4 else (if i.val < 1190 then 40 else 75)) else (if i.val < 1192 then 80 else (if i.val < 1193 then 6 else 59))) else (if i.val < 1197 then (if i.val < 1195 then 48 else (if i.val < 1196 then 8 else 69)) else (if i.val < 1199 then (if i.val < 1198 then 80 else 58) else (if i.val < 1200 then 81 else 48)))) else (if i.val < 1208 then (if i.val < 1204 then (if i.val < 1202 then 71 else (if i.val < 1203 then 40 else 80)) else (if i.val < 1206 then (if i.val < 1205 then 48 else 59) else (if i.val < 1207 then 37 else 78))) else (if i.val < 1211 then (if i.val < 1209 then 100 else (if i.val < 1210 then 35 else 41)) else (if i.val < 1213 then (if i.val < 1212 then 100 else 55) else (if i.val < 1214 then 55 else 41))))) else (if i.val < 1228 then (if i.val < 1221 then (if i.val < 1218 then (if i.val < 1216 then 41 else (if i.val < 1217 then 44 else 55)) else (if i.val < 1219 then 55 else (if i.val < 1220 then 41 else 55))) else (if i.val < 1224 then (if i.val < 1222 then 34 else (if i.val < 1223 then 55 else 34)) else (if i.val < 1226 then (if i.val < 1225 then 76 else 85) else (if i.val < 1227 then 55 else 41)))) else (if i.val < 1235 then (if i.val < 1231 then (if i.val < 1229 then 20 else (if i.val < 1230 then 41 else 44)) else (if i.val < 1233 then (if i.val < 1232 then 55 else 25) else (if i.val < 1234 then 25 else 85))) else (if i.val < 1238 then (if i.val < 1236 then 41 else (if i.val < 1237 then 41 else 55)) else (if i.val < 1240 then (if i.val < 1239 then 25 else 85) else (if i.val < 1241 then 65 else 55)))))) else (if i.val < 1269 then (if i.val < 1255 then (if i.val < 1248 then (if i.val < 1245 then (if i.val < 1243 then 20 else (if i.val < 1244 then 25 else 35)) else (if i.val < 1246 then 76 else (if i.val < 1247 then 32 else 25))) else (if i.val < 1251 then (if i.val < 1249 then 20 else (if i.val < 1250 then 25 else 32)) else (if i.val < 1253 then (if i.val < 1252 then 41 else 20) else (if i.val < 1254 then 41 else 24)))) else (if i.val < 1262 then (if i.val < 1258 then (if i.val < 1256 then 24 else (if i.val < 1257 then 25 else 25)) else (if i.val < 1260 then (if i.val < 1259 then 25 else 27) else (if i.val < 1261 then 85 else 56))) else (if i.val < 1265 then (if i.val < 1263 then 20 else (if i.val < 1264 then 41 else 24)) else (if i.val < 1267 then (if i.val < 1266 then 25 else 25) else (if i.val < 1268 then 41 else 25))))) else (if i.val < 1282 then (if i.val < 1275 then (if i.val < 1272 then (if i.val < 1270 then 32 else (if i.val < 1271 then 25 else 56)) else (if i.val < 1273 then 20 else (if i.val < 1274 then 24 else 25))) else (if i.val < 1278 then (if i.val < 1276 then 27 else (if i.val < 1277 then 25 else 32)) else (if i.val < 1280 then (if i.val < 1279 then 35 else 77) else (if i.val < 1281 then 25 else 20)))) else (if i.val < 1289 then (if i.val < 1285 then (if i.val < 1283 then 66 else (if i.val < 1284 then 43 else 25)) else (if i.val < 1287 then (if i.val < 1286 then 51 else 55) else (if i.val < 1288 then 35 else 15))) else (if i.val < 1292 then (if i.val < 1290 then 100 else (if i.val < 1291 then 35 else 78)) else (if i.val < 1294 then (if i.val < 1293 then 66 else 78) else (if i.val < 1295 then 90 else 32))))))))) else (if i.val < 1512 then (if i.val < 1404 then (if i.val < 1350 then (if i.val < 1323 then (if i.val < 1309 then (if i.val < 1302 then (if i.val < 1299 then (if i.val < 1297 then 43 else (if i.val < 1298 then 90 else 20)) else (if i.val < 1300 then 55 else (if i.val < 1301 then 35 else 90))) else (if i.val < 1305 then (if i.val < 1303 then 43 else (if i.val < 1304 then 55 else 43)) else (if i.val < 1307 then (if i.val < 1306 then 55 else 15) else (if i.val < 1308 then 90 else 77)))) else (if i.val < 1316 then (if i.val < 1312 then (if i.val < 1310 then 43 else (if i.val < 1311 then 85 else 27)) else (if i.val < 1314 then (if i.val < 1313 then 25 else 35) else (if i.val < 1315 then 78 else 32))) else (if i.val < 1319 then (if i.val < 1317 then 25 else (if i.val < 1318 then 43 else 85)) else (if i.val < 1321 then (if i.val < 1320 then 43 else 85) else (if i.val < 1322 then 25 else 51))))) else (if i.val < 1336 then (if i.val < 1329 then (if i.val < 1326 then (if i.val < 1324 then 66 else (if i.val < 1325 then 78 else 20)) else (if i.val < 1327 then 27 else (if i.val < 1328 then 55 else 51))) else (if i.val < 1332 then (if i.val < 1330 then 66 else (if i.val < 1331 then 55 else 100)) else (if i.val < 1334 then (if i.val < 1333 then 35 else 66) else (if i.val < 1335 then 32 else 90)))) else (if i.val < 1343 then (if i.val < 1339 then (if i.val < 1337 then 55 else (if i.val < 1338 then 90 else 35)) else (if i.val < 1341 then (if i.val < 1340 then 90 else 43) else (if i.val < 1342 then 100 else 90))) else (if i.val < 1346 then (if i.val < 1344 then 43 else (if i.val < 1345 then 77 else 77)) else (if i.val < 1348 then (if i.val < 1347 then 32 else 34) else (if i.val < 1349 then 78 else 34)))))) else (if i.val < 1377 then (if i.val < 1363 then (if i.val < 1356 then (if i.val < 1353 then (if i.val < 1351 then 20 else (if i.val < 1352 then 78 else 55)) else (if i.val < 1354 then 20 else (if i.val < 1355 then 55 else 90))) else (if i.val < 1359 then (if i.val < 1357 then 100 else (if i.val < 1358 then 90 else 34)) else (if i.val < 1361 then (if i.val < 1360 then 27 else 34) else (if i.val < 1362 then 20 else 34)))) else (if i.val < 1370 then (if i.val < 1366 then (if i.val < 1364 then 41 else (if i.val < 1365 then 34 else 20)) else (if i.val < 1368 then (if i.val < 1367 then 66 else 34) else (if i.val < 1369 then 41 else 20))) else (if i.val < 1373 then (if i.val < 1371 then 55 else (if i.val < 1372 then 34 else 90)) else (if i.val < 1375 then (if i.val < 1374 then 34 else 41) else (if i.val < 1376 then 34 else 20))))) else (if i.val < 1390 then (if i.val < 1383 then (if i.val < 1380 then (if i.val < 1378 then 27 else (if i.val < 1379 then 55 else 34)) else (if i.val < 1381 then 90 else (if i.val < 1382 then 66 else 77))) else (if i.val < 1386 then (if i.val < 1384 then 34 else (if i.val < 1385 then 41 else 55)) else (if i.val < 1388 then (if i.val < 1387 then 20 else 27) else (if i.val < 1389 then 34 else 78)))) else (if i.val < 1397 then (if i.val < 1393 then (if i.val < 1391 then 20 else (if i.val < 1392 then 55 else 85)) else (if i.val < 1395 then (if i.val < 1394 then 41 else 51) else (if i.val < 1396 then 78 else 20))) else (if i.val < 1400 then (if i.val < 1398 then 27 else (if i.val < 1399 then 34 else 41)) else (if i.val < 1402 then (if i.val < 1401 then 20 else 41) else (if i.val < 1403 then 55 else 20))))))) else (if i.val < 1458 then (if i.val < 1431 then (if i.val < 1417 then (if i.val < 1410 then (if i.val < 1407 then (if i.val < 1405 then 27 else (if i.val < 1406 then 34 else 44)) else (if i.val < 1408 then 28 else (if i.val < 1409 then 44 else 51))) else (if i.val < 1413 then (if i.val < 1411 then 31 else (if i.val < 1412 then 27 else 31)) else (if i.val < 1415 then (if i.val < 1414 then 27 else 34) else (if i.val < 1416 then 55 else 35)))) else (if i.val < 1424 then (if i.val < 1420 then (if i.val < 1418 then 44 else (if i.val < 1419 then 51 else 31)) else (if i.val < 1422 then (if i.val < 1421 then 51 else 65) else (if i.val < 1423 then 19 else 27))) else (if i.val < 1427 then (if i.val < 1425 then 31 else (if i.val < 1426 then 25 else 32)) else (if i.val < 1429 then (if i.val < 1428 then 41 else 77) else (if i.val < 1430 then 27 else 31))))) else (if i.val < 1444 then (if i.val < 1437 then (if i.val < 1434 then (if i.val < 1432 then 27 else (if i.val < 1433 then 31 else 31)) else (if i.val < 1435 then 27 else (if i.val < 1436 then 28 else 31))) else (if i.val < 1440 then (if i.val < 1438 then 19 else (if i.val < 1439 then 35 else 31)) else (if i.val < 1442 then (if i.val < 1441 then 19 else 28) else (if i.val < 1443 then 20 else 27)))) else (if i.val < 1451 then (if i.val < 1447 then (if i.val < 1445 then 34 else (if i.val < 1446 then 44 else 32)) else (if i.val < 1449 then (if i.val < 1448 then 31 else 44) else (if i.val < 1450 then 25 else 32))) else (if i.val < 1454 then (if i.val < 1452 then 31 else (if i.val < 1453 then 41 else 32)) else (if i.val < 1456 then (if i.val < 1455 then 25 else 66) else (if i.val < 1457 then 77 else 20)))))) else (if i.val < 1485 then (if i.val < 1471 then (if i.val < 1464 then (if i.val < 1461 then (if i.val < 1459 then 35 else (if i.val < 1460 then 35 else 20)) else (if i.val < 1462 then 35 else (if i.val < 1463 then 20 else 51))) else (if i.val < 1467 then (if i.val < 1465 then 56 else (if i.val < 1466 then 35 else 41)) else (if i.val < 1469 then (if i.val < 1468 then 35 else 66) else (if i.val < 1470 then 27 else 56)))) else (if i.val < 1478 then (if i.val < 1474 then (if i.val < 1472 then 32 else (if i.val < 1473 then 32 else 44)) else (if i.val < 1476 then (if i.val < 1475 then 32 else 25) else (if i.val < 1477 then 41 else 31))) else (if i.val < 1481 then (if i.val < 1479 then 19 else (if i.val < 1480 then 28 else 41)) else (if i.val < 1483 then (if i.val < 1482 then 20 else 35) else (if i.val < 1484 then 32 else 20))))) else (if i.val < 1498 then (if i.val < 1491 then (if i.val < 1488 then (if i.val < 1486 then 77 else (if i.val < 1487 then 25 else 20)) else (if i.val < 1489 then 41 else (if i.val < 1490 then 32 else 20))) else (if i.val < 1494 then (if i.val < 1492 then 25 else (if i.val < 1493 then 41 else 32)) else (if i.val < 1496 then (if i.val < 1495 then 25 else 35) else (if i.val < 1497 then 35 else 15)))) else (if i.val < 1505 then (if i.val < 1501 then (if i.val < 1499 then 25 else (if i.val < 1500 then 11 else 20)) else (if i.val < 1503 then (if i.val < 1502 then 11 else 15) else (if i.val < 1504 then 20 else 35))) else (if i.val < 1508 then (if i.val < 1506 then 43 else (if i.val < 1507 then 27 else 35)) else (if i.val < 1510 then (if i.val < 1509 then 43 else 87) else (if i.val < 1511 then 67 else 87)))))))) else (if i.val < 1620 then (if i.val < 1566 then (if i.val < 1539 then (if i.val < 1525 then (if i.val < 1518 then (if i.val < 1515 then (if i.val < 1513 then 17 else (if i.val < 1514 then 7 else 67)) else (if i.val < 1516 then 17 else (if i.val < 1517 then 17 else 17))) else (if i.val < 1521 then (if i.val < 1519 then 24 else (if i.val < 1520 then 24 else 17)) else (if i.val < 1523 then (if i.val < 1522 then 7 else 24) else (if i.val < 1524 then 17 else 24)))) else (if i.val < 1532 then (if i.val < 1528 then (if i.val < 1526 then 10 else (if i.val < 1527 then 86 else 78)) else (if i.val < 1530 then (if i.val < 1529 then 87 else 78) else (if i.val < 1531 then 86 else 91))) else (if i.val < 1535 then (if i.val < 1533 then 17 else (if i.val < 1534 then 17 else 74)) else (if i.val < 1537 then (if i.val < 1536 then 24 else 24) else (if i.val < 1538 then 72 else 78))))) else (if i.val < 1552 then (if i.val < 1545 then (if i.val < 1542 then (if i.val < 1540 then 17 else (if i.val < 1541 then 74 else 24)) else (if i.val < 1543 then 91 else (if i.val < 1544 then 74 else 86))) else (if i.val < 1548 then (if i.val < 1546 then 78 else (if i.val < 1547 then 17 else 24)) else (if i.val < 1550 then (if i.val < 1549 then 72 else 10) else (if i.val < 1551 then 61 else 87)))) else (if i.val < 1559 then (if i.val < 1555 then (if i.val < 1553 then 84 else (if i.val < 1554 then 29 else 72)) else (if i.val < 1557 then (if i.val < 1556 then 7 else 84) else (if i.val < 1558 then 29 else 61))) else (if i.val < 1562 then (if i.val < 1560 then 7 else (if i.val < 1561 then 29 else 7)) else (if i.val < 1564 then (if i.val < 1563 then 72 else 78) else (if i.val < 1565 then 74 else 72)))))) else (if i.val < 1593 then (if i.val < 1579 then (if i.val < 1572 then (if i.val < 1569 then (if i.val < 1567 then 29 else (if i.val < 1568 then 7 else 78)) else (if i.val < 1570 then 7 else (if i.val < 1571 then 61 else 72))) else (if i.val < 1575 then (if i.val < 1573 then 7 else (if i.val < 1574 then 72 else 4)) else (if i.val < 1577 then (if i.val < 1576 then 4 else 7) else (if i.val < 1578 then 87 else 79)))) else (if i.val < 1586 then (if i.val < 1582 then (if i.val < 1580 then 52 else (if i.val < 1581 then 7 else 52)) else (if i.val < 1584 then (if i.val < 1583 then 52 else 67) else (if i.val < 1585 then 52 else 64))) else (if i.val < 1589 then (if i.val < 1587 then 13 else (if i.val < 1588 then 45 else 79)) else (if i.val < 1591 then (if i.val < 1590 then 52 else 52) else (if i.val < 1592 then 87 else 79))))) else (if i.val < 1606 then (if i.val < 1599 then (if i.val < 1596 then (if i.val < 1594 then 7 else (if i.val < 1595 then 52 else 45)) else (if i.val < 1597 then 61 else (if i.val < 1598 then 52 else 61))) else (if i.val < 1602 then (if i.val < 1600 then 7 else (if i.val < 1601 then 7 else 52)) else (if i.val < 1604 then (if i.val < 1603 then 7 else 72) else (if i.val < 1605 then 91 else 7)))) else (if i.val < 1613 then (if i.val < 1609 then (if i.val < 1607 then 52 else (if i.val < 1608 then 64 else 64)) else (if i.val < 1611 then (if i.val < 1610 then 79 else 82) else (if i.val < 1612 then 61 else 7))) else (if i.val < 1616 then (if i.val < 1614 then 52 else (if i.val < 1615 then 67 else 52)) else (if i.val < 1618 then (if i.val < 1617 then 13 else 45) else (if i.val < 1619 then 74 else 45))))))) else (if i.val < 1674 then (if i.val < 1647 then (if i.val < 1633 then (if i.val < 1626 then (if i.val < 1623 then (if i.val < 1621 then 61 else (if i.val < 1622 then 7 else 84)) else (if i.val < 1624 then 17 else (if i.val < 1625 then 61 else 45))) else (if i.val < 1629 then (if i.val < 1627 then 74 else (if i.val < 1628 then 84 else 45)) else (if i.val < 1631 then (if i.val < 1630 then 74 else 84) else (if i.val < 1632 then 17 else 45)))) else (if i.val < 1640 then (if i.val < 1636 then (if i.val < 1634 then 61 else (if i.val < 1635 then 84 else 17)) else (if i.val < 1638 then (if i.val < 1637 then 24 else 45) else (if i.val < 1639 then 45 else 84))) else (if i.val < 1643 then (if i.val < 1641 then 24 else (if i.val < 1642 then 10 else 45)) else (if i.val < 1645 then (if i.val < 1644 then 61 else 84) else (if i.val < 1646 then 74 else 72))))) else (if i.val < 1660 then (if i.val < 1653 then (if i.val < 1650 then (if i.val < 1648 then 64 else (if i.val < 1649 then 17 else 10)) else (if i.val < 1651 then 61 else (if i.val < 1652 then 17 else 74))) else (if i.val < 1656 then (if i.val < 1654 then 88 else (if i.val < 1655 then 88 else 84)) else (if i.val < 1658 then (if i.val < 1657 then 17 else 74) else (if i.val < 1659 then 88 else 84)))) else (if i.val < 1667 then (if i.val < 1663 then (if i.val < 1661 then 74 else (if i.val < 1662 then 84 else 84)) else (if i.val < 1665 then (if i.val < 1664 then 84 else 74) else (if i.val < 1666 then 24 else 17))) else (if i.val < 1670 then (if i.val < 1668 then 24 else (if i.val < 1669 then 84 else 88)) else (if i.val < 1672 then (if i.val < 1671 then 10 else 29) else (if i.val < 1673 then 10 else 29)))))) else (if i.val < 1701 then (if i.val < 1687 then (if i.val < 1680 then (if i.val < 1677 then (if i.val < 1675 then 1 else (if i.val < 1676 then 48 else 1)) else (if i.val < 1678 then 59 else (if i.val < 1679 then 59 else 58))) else (if i.val < 1683 then (if i.val < 1681 then 48 else (if i.val < 1682 then 59 else 59)) else (if i.val < 1685 then (if i.val < 1684 then 59 else 58) else (if i.val < 1686 then 40 else 50)))) else (if i.val < 1694 then (if i.val < 1690 then (if i.val < 1688 then 3 else (if i.val < 1689 then 40 else 50)) else (if i.val < 1692 then (if i.val < 1691 then 63 else 50) else (if i.val < 1693 then 89 else 58))) else (if i.val < 1697 then (if i.val < 1695 then 89 else (if i.val < 1696 then 50 else 89)) else (if i.val < 1699 then (if i.val < 1698 then 3 else 58) else (if i.val < 1700 then 3 else 63))))) else (if i.val < 1714 then (if i.val < 1707 then (if i.val < 1704 then (if i.val < 1702 then 89 else (if i.val < 1703 then 3 else 1)) else (if i.val < 1705 then 6 else (if i.val < 1706 then 59 else 6))) else (if i.val < 1710 then (if i.val < 1708 then 4 else (if i.val < 1709 then 40 else 4)) else (if i.val < 1712 then (if i.val < 1711 then 6 else 6) else (if i.val < 1713 then 1 else 59)))) else (if i.val < 1721 then (if i.val < 1717 then (if i.val < 1715 then 6 else (if i.val < 1716 then 81 else 59)) else (if i.val < 1719 then (if i.val < 1718 then 48 else 6) else (if i.val < 1720 then 75 else 50))) else (if i.val < 1724 then (if i.val < 1722 then 75 else (if i.val < 1723 then 50 else 55)) else (if i.val < 1726 then (if i.val < 1725 then 55 else 55) else (if i.val < 1727 then 15 else 43)))))))))))

def g32p_supplierGroup02_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 15, 17, 18, 19, 20, 23, 24, 25, 27, 28, 29, 31, 32, 34, 35, 37, 40, 41, 43, 44, 45, 48, 50, 51, 52, 55, 56, 58, 59, 61, 63, 64, 65, 66, 67, 69, 71, 72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup02_matrix_000 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 0 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 0 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 0 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 0 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 0 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_001 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 1 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 1 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 1 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 1 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 1 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_002 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 2 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 2 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 2 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 2 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 2 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_003 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 3 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 3 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 3 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 3 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 3 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_004 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 4 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 4 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 4 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 4 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 4 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_005 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 5 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 5 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 5 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 5 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 5 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_006 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 6 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 6 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 6 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 6 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 6 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_007 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 7 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 7 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 7 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 7 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 7 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_008 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 8 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 8 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 8 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 8 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 8 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_009 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 9 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 9 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 9 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 9 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 9 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_010 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 10 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 10 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 10 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 10 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 10 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_011 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 11 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 11 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 11 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 11 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 11 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_012 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 12 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 12 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 12 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 12 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 12 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_013 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 13 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 13 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 13 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 13 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 13 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_014 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 14 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 14 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 14 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 14 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 14 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_015 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 15 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 15 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 15 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 15 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 15 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup02_matrix_016 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 16 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 16 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 16 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 16 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 16 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_017 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 17 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 17 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 17 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 17 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 17 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_018 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 18 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 18 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 18 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 18 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 18 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_019 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 19 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 19 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 19 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 19 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 19 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_020 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 20 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 20 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 20 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 20 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 20 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_021 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 21 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 21 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 21 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 21 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 21 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_022 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 22 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 22 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 22 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 22 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 22 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_023 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 23 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 23 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 23 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 23 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 23 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_024 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 24 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 24 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 24 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 24 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 24 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_025 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 25 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 25 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 25 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 25 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 25 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_026 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 26 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 26 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 26 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 26 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 26 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_027 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 27 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 27 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 27 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_027 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 27 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 27 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 27 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_027 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 27 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_028 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 28 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 28 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 28 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_028 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 28 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 28 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 28 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_028 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 28 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_029 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 29 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 29 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 29 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_029 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 29 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 29 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 29 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_029 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 29 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_030 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 30 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 30 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 30 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_030 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 30 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 30 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 30 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_030 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 30 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_031 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 31 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 31 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 31 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_031 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 31 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 31 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 31 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_031 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 31 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup02_matrix_032 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 32 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 32 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 32 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_032 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 32 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 32 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 32 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_032 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 32 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_033 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 33 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 33 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 33 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_033 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 33 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 33 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 33 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_033 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 33 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_034 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 34 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 34 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 34 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_034 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 34 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 34 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 34 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_034 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 34 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_035 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 35 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 35 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 35 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_035 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 35 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 35 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 35 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_035 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 35 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_036 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 36 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 36 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 36 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_036 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 36 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 36 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 36 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_036 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 36 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_037 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 37 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 37 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 37 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_037 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 37 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 37 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 37 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_037 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 37 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_038 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 38 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 38 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 38 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_038 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 38 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 38 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 38 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_038 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 38 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_039 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 39 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 39 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 39 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_039 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 39 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 39 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 39 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_039 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 39 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_040 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 40 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 40 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 40 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_040 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 40 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 40 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 40 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_040 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 40 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_041 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 41 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 41 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 41 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_041 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 41 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 41 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 41 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_041 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 41 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_042 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 42 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 42 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 42 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_042 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 42 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 42 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 42 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_042 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 42 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_043 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 43 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 43 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 43 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_043 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 43 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 43 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 43 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_043 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 43 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_044 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 44 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 44 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 44 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_044 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 44 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 44 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 44 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_044 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 44 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_045 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 45 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 45 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 45 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_045 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 45 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 45 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 45 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_045 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 45 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_046 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 46 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 46 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 46 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_046 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 46 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 46 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 46 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_046 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 46 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_047 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 47 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 47 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 47 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_047 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 47 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 47 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 47 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_047 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 47 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup02_matrix_048 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 48 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 48 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 48 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_048 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 48 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 48 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 48 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_048 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 48 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_049 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 49 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 49 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 49 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_049 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 49 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 49 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 49 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_049 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 49 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_050 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 50 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 50 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 50 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_050 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 50 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 50 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 50 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_050 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 50 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_051 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 51 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 51 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 51 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_051 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 51 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 51 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 51 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_051 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 51 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_052 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 52 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 52 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 52 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_052 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 52 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 52 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 52 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_052 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 52 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_053 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 53 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 53 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 53 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_053 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 53 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 53 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 53 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_053 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 53 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_054 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 54 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 54 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 54 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_054 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 54 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 54 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 54 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_054 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 54 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_055 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 55 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 55 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 55 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_055 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 55 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 55 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 55 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_055 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 55 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_056 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 56 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 56 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 56 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_056 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 56 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 56 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 56 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_056 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 56 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_057 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 57 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 57 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 57 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_057 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 57 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 57 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 57 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_057 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 57 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_058 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 58 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 58 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 58 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_058 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 58 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 58 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 58 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_058 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 58 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_059 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 59 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 59 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 59 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_059 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 59 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 59 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 59 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_059 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 59 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_060 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 60 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 60 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 60 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_060 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 60 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 60 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 60 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_060 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 60 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_061 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 61 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 61 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 61 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_061 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 61 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 61 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 61 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_061 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 61 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_062 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 62 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 62 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 62 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_062 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 62 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 62 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 62 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_062 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 62 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_063 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 63 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 63 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 63 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_063 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 63 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 63 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 63 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_063 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 63 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup02_matrix_064 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 64 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 64 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 64 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_064 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 64 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 64 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 64 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_064 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 64 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_065 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 65 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 65 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 65 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_065 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 65 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 65 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 65 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_065 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 65 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_066 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 66 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 66 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 66 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_066 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 66 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 66 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 66 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_066 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 66 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_067 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 67 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 67 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 67 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_067 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 67 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 67 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 67 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_067 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 67 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_068 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 68 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 68 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 68 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_068 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 68 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 68 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 68 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_068 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 68 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_069 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 69 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 69 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 69 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_069 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 69 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 69 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 69 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_069 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 69 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_070 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 70 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 70 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 70 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_070 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 70 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 70 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 70 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_070 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 70 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_071 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 71 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 71 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 71 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_071 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 71 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 71 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 71 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_071 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 71 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_072 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 72 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 72 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 72 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_072 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 72 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 72 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 72 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_072 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 72 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_073 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 73 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 73 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 73 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_073 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 73 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 73 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 73 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_073 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 73 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_074 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 74 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 74 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 74 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_074 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 74 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 74 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 74 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_074 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 74 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_075 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 75 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 75 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 75 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_075 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 75 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 75 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 75 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_075 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 75 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_076 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 76 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 76 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 76 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_076 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 76 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 76 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 76 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_076 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 76 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_077 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 77 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 77 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 77 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_077 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 77 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 77 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 77 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_077 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 77 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_078 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 78 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 78 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 78 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_078 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 78 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 78 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 78 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_078 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 78 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_079 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 79 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 79 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 79 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_079 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 79 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 79 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 79 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_079 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 79 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup02_matrix_080 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 80 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 80 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 80 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_080 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 80 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 80 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 80 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_080 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 80 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_081 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 81 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 81 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 81 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_081 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 81 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 81 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 81 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_081 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 81 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_082 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 82 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 82 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 82 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_082 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 82 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 82 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 82 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_082 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 82 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_083 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 83 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 83 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 83 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_083 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 83 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 83 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 83 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_083 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 83 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_084 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 84 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 84 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 84 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_084 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 84 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 84 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 84 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_084 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 84 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_085 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 85 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 85 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 85 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_085 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 85 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 85 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 85 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_085 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 85 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_086 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 86 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 86 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 86 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_086 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 86 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 86 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 86 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_086 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 86 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_087 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 87 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 87 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 87 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_087 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 87 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 87 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 87 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_087 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 87 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_088 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 88 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 88 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 88 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_088 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 88 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 88 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 88 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_088 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 88 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_089 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 89 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 89 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 89 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_089 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 89 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 89 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 89 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_089 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 89 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_090 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 90 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 90 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 90 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_090 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 90 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 90 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 90 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_090 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 90 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_091 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 91 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 91 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 91 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_091 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 91 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 91 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 91 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_091 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 91 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_092 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 92 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 92 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 92 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_092 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 92 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 92 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 92 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_092 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 92 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_093 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 93 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 93 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 93 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_093 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 93 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 93 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 93 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_093 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 93 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_094 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 94 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 94 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 94 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_094 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 94 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 94 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 94 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_094 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 94 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_095 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 95 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 95 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 95 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_095 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 95 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 95 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 95 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_095 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 95 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup02_matrix_096 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 96 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 96 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 96 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_096 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 96 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 96 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 96 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_096 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 96 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_097 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 97 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 97 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 97 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_097 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 97 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 97 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 97 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_097 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 97 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_098 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 98 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 98 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 98 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_098 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 98 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 98 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 98 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_098 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 98 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_099 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 99 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 99 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 99 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_099 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 99 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 99 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 99 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_099 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 99 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_100 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 100 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 100 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 100 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_100 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 100 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 100 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 100 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_100 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 100 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_101 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 101 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 101 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 101 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_101 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 101 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 101 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 101 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_101 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 101 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_102 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 102 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 102 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 102 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_102 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 102 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 102 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 102 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_102 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 102 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_103 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 103 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 103 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 103 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_103 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 103 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 103 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 103 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_103 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 103 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_104 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 104 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 104 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 104 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_104 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 104 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 104 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 104 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_104 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 104 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_105 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 105 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 105 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 105 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_105 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 105 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 105 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 105 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_105 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 105 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_106 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 106 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 106 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 106 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_106 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 106 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 106 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 106 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_106 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 106 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

theorem g32p_supplierGroup02_matrix_107 : ∀ r : Fin 16,
    g32p_row04_groupNodes (g32p_finBlockIndex 1728 107 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 107 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 107 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup02_class_107 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 107 r)).1 (g32p_supplierGroup02_source (g32p_finBlockIndex 1728 107 r)).2 =
      g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 107 r) := by
  decide +kernel

theorem g32p_supplierGroup02_support_107 : ∀ r : Fin 16,
    g32p_supplierGroup02_classify (g32p_finBlockIndex 1728 107 r) ∈ g32p_supplierGroup02_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup02_matrix (i : Fin 1728) :
    g32p_row04_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source i).1 (g32p_supplierGroup02_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row04_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup02_source i).1 (g32p_supplierGroup02_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup02_matrix_000 r
  · exact g32p_supplierGroup02_matrix_001 r
  · exact g32p_supplierGroup02_matrix_002 r
  · exact g32p_supplierGroup02_matrix_003 r
  · exact g32p_supplierGroup02_matrix_004 r
  · exact g32p_supplierGroup02_matrix_005 r
  · exact g32p_supplierGroup02_matrix_006 r
  · exact g32p_supplierGroup02_matrix_007 r
  · exact g32p_supplierGroup02_matrix_008 r
  · exact g32p_supplierGroup02_matrix_009 r
  · exact g32p_supplierGroup02_matrix_010 r
  · exact g32p_supplierGroup02_matrix_011 r
  · exact g32p_supplierGroup02_matrix_012 r
  · exact g32p_supplierGroup02_matrix_013 r
  · exact g32p_supplierGroup02_matrix_014 r
  · exact g32p_supplierGroup02_matrix_015 r
  · exact g32p_supplierGroup02_matrix_016 r
  · exact g32p_supplierGroup02_matrix_017 r
  · exact g32p_supplierGroup02_matrix_018 r
  · exact g32p_supplierGroup02_matrix_019 r
  · exact g32p_supplierGroup02_matrix_020 r
  · exact g32p_supplierGroup02_matrix_021 r
  · exact g32p_supplierGroup02_matrix_022 r
  · exact g32p_supplierGroup02_matrix_023 r
  · exact g32p_supplierGroup02_matrix_024 r
  · exact g32p_supplierGroup02_matrix_025 r
  · exact g32p_supplierGroup02_matrix_026 r
  · exact g32p_supplierGroup02_matrix_027 r
  · exact g32p_supplierGroup02_matrix_028 r
  · exact g32p_supplierGroup02_matrix_029 r
  · exact g32p_supplierGroup02_matrix_030 r
  · exact g32p_supplierGroup02_matrix_031 r
  · exact g32p_supplierGroup02_matrix_032 r
  · exact g32p_supplierGroup02_matrix_033 r
  · exact g32p_supplierGroup02_matrix_034 r
  · exact g32p_supplierGroup02_matrix_035 r
  · exact g32p_supplierGroup02_matrix_036 r
  · exact g32p_supplierGroup02_matrix_037 r
  · exact g32p_supplierGroup02_matrix_038 r
  · exact g32p_supplierGroup02_matrix_039 r
  · exact g32p_supplierGroup02_matrix_040 r
  · exact g32p_supplierGroup02_matrix_041 r
  · exact g32p_supplierGroup02_matrix_042 r
  · exact g32p_supplierGroup02_matrix_043 r
  · exact g32p_supplierGroup02_matrix_044 r
  · exact g32p_supplierGroup02_matrix_045 r
  · exact g32p_supplierGroup02_matrix_046 r
  · exact g32p_supplierGroup02_matrix_047 r
  · exact g32p_supplierGroup02_matrix_048 r
  · exact g32p_supplierGroup02_matrix_049 r
  · exact g32p_supplierGroup02_matrix_050 r
  · exact g32p_supplierGroup02_matrix_051 r
  · exact g32p_supplierGroup02_matrix_052 r
  · exact g32p_supplierGroup02_matrix_053 r
  · exact g32p_supplierGroup02_matrix_054 r
  · exact g32p_supplierGroup02_matrix_055 r
  · exact g32p_supplierGroup02_matrix_056 r
  · exact g32p_supplierGroup02_matrix_057 r
  · exact g32p_supplierGroup02_matrix_058 r
  · exact g32p_supplierGroup02_matrix_059 r
  · exact g32p_supplierGroup02_matrix_060 r
  · exact g32p_supplierGroup02_matrix_061 r
  · exact g32p_supplierGroup02_matrix_062 r
  · exact g32p_supplierGroup02_matrix_063 r
  · exact g32p_supplierGroup02_matrix_064 r
  · exact g32p_supplierGroup02_matrix_065 r
  · exact g32p_supplierGroup02_matrix_066 r
  · exact g32p_supplierGroup02_matrix_067 r
  · exact g32p_supplierGroup02_matrix_068 r
  · exact g32p_supplierGroup02_matrix_069 r
  · exact g32p_supplierGroup02_matrix_070 r
  · exact g32p_supplierGroup02_matrix_071 r
  · exact g32p_supplierGroup02_matrix_072 r
  · exact g32p_supplierGroup02_matrix_073 r
  · exact g32p_supplierGroup02_matrix_074 r
  · exact g32p_supplierGroup02_matrix_075 r
  · exact g32p_supplierGroup02_matrix_076 r
  · exact g32p_supplierGroup02_matrix_077 r
  · exact g32p_supplierGroup02_matrix_078 r
  · exact g32p_supplierGroup02_matrix_079 r
  · exact g32p_supplierGroup02_matrix_080 r
  · exact g32p_supplierGroup02_matrix_081 r
  · exact g32p_supplierGroup02_matrix_082 r
  · exact g32p_supplierGroup02_matrix_083 r
  · exact g32p_supplierGroup02_matrix_084 r
  · exact g32p_supplierGroup02_matrix_085 r
  · exact g32p_supplierGroup02_matrix_086 r
  · exact g32p_supplierGroup02_matrix_087 r
  · exact g32p_supplierGroup02_matrix_088 r
  · exact g32p_supplierGroup02_matrix_089 r
  · exact g32p_supplierGroup02_matrix_090 r
  · exact g32p_supplierGroup02_matrix_091 r
  · exact g32p_supplierGroup02_matrix_092 r
  · exact g32p_supplierGroup02_matrix_093 r
  · exact g32p_supplierGroup02_matrix_094 r
  · exact g32p_supplierGroup02_matrix_095 r
  · exact g32p_supplierGroup02_matrix_096 r
  · exact g32p_supplierGroup02_matrix_097 r
  · exact g32p_supplierGroup02_matrix_098 r
  · exact g32p_supplierGroup02_matrix_099 r
  · exact g32p_supplierGroup02_matrix_100 r
  · exact g32p_supplierGroup02_matrix_101 r
  · exact g32p_supplierGroup02_matrix_102 r
  · exact g32p_supplierGroup02_matrix_103 r
  · exact g32p_supplierGroup02_matrix_104 r
  · exact g32p_supplierGroup02_matrix_105 r
  · exact g32p_supplierGroup02_matrix_106 r
  · exact g32p_supplierGroup02_matrix_107 r

theorem g32p_supplierGroup02_class (i : Fin 1728) :
    g32p_supplierForest_classes (g32p_supplierGroup02_source i).1 (g32p_supplierGroup02_source i).2 =
      g32p_supplierGroup02_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup02_source i).1 (g32p_supplierGroup02_source i).2 =
      g32p_supplierGroup02_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup02_class_000 r
  · exact g32p_supplierGroup02_class_001 r
  · exact g32p_supplierGroup02_class_002 r
  · exact g32p_supplierGroup02_class_003 r
  · exact g32p_supplierGroup02_class_004 r
  · exact g32p_supplierGroup02_class_005 r
  · exact g32p_supplierGroup02_class_006 r
  · exact g32p_supplierGroup02_class_007 r
  · exact g32p_supplierGroup02_class_008 r
  · exact g32p_supplierGroup02_class_009 r
  · exact g32p_supplierGroup02_class_010 r
  · exact g32p_supplierGroup02_class_011 r
  · exact g32p_supplierGroup02_class_012 r
  · exact g32p_supplierGroup02_class_013 r
  · exact g32p_supplierGroup02_class_014 r
  · exact g32p_supplierGroup02_class_015 r
  · exact g32p_supplierGroup02_class_016 r
  · exact g32p_supplierGroup02_class_017 r
  · exact g32p_supplierGroup02_class_018 r
  · exact g32p_supplierGroup02_class_019 r
  · exact g32p_supplierGroup02_class_020 r
  · exact g32p_supplierGroup02_class_021 r
  · exact g32p_supplierGroup02_class_022 r
  · exact g32p_supplierGroup02_class_023 r
  · exact g32p_supplierGroup02_class_024 r
  · exact g32p_supplierGroup02_class_025 r
  · exact g32p_supplierGroup02_class_026 r
  · exact g32p_supplierGroup02_class_027 r
  · exact g32p_supplierGroup02_class_028 r
  · exact g32p_supplierGroup02_class_029 r
  · exact g32p_supplierGroup02_class_030 r
  · exact g32p_supplierGroup02_class_031 r
  · exact g32p_supplierGroup02_class_032 r
  · exact g32p_supplierGroup02_class_033 r
  · exact g32p_supplierGroup02_class_034 r
  · exact g32p_supplierGroup02_class_035 r
  · exact g32p_supplierGroup02_class_036 r
  · exact g32p_supplierGroup02_class_037 r
  · exact g32p_supplierGroup02_class_038 r
  · exact g32p_supplierGroup02_class_039 r
  · exact g32p_supplierGroup02_class_040 r
  · exact g32p_supplierGroup02_class_041 r
  · exact g32p_supplierGroup02_class_042 r
  · exact g32p_supplierGroup02_class_043 r
  · exact g32p_supplierGroup02_class_044 r
  · exact g32p_supplierGroup02_class_045 r
  · exact g32p_supplierGroup02_class_046 r
  · exact g32p_supplierGroup02_class_047 r
  · exact g32p_supplierGroup02_class_048 r
  · exact g32p_supplierGroup02_class_049 r
  · exact g32p_supplierGroup02_class_050 r
  · exact g32p_supplierGroup02_class_051 r
  · exact g32p_supplierGroup02_class_052 r
  · exact g32p_supplierGroup02_class_053 r
  · exact g32p_supplierGroup02_class_054 r
  · exact g32p_supplierGroup02_class_055 r
  · exact g32p_supplierGroup02_class_056 r
  · exact g32p_supplierGroup02_class_057 r
  · exact g32p_supplierGroup02_class_058 r
  · exact g32p_supplierGroup02_class_059 r
  · exact g32p_supplierGroup02_class_060 r
  · exact g32p_supplierGroup02_class_061 r
  · exact g32p_supplierGroup02_class_062 r
  · exact g32p_supplierGroup02_class_063 r
  · exact g32p_supplierGroup02_class_064 r
  · exact g32p_supplierGroup02_class_065 r
  · exact g32p_supplierGroup02_class_066 r
  · exact g32p_supplierGroup02_class_067 r
  · exact g32p_supplierGroup02_class_068 r
  · exact g32p_supplierGroup02_class_069 r
  · exact g32p_supplierGroup02_class_070 r
  · exact g32p_supplierGroup02_class_071 r
  · exact g32p_supplierGroup02_class_072 r
  · exact g32p_supplierGroup02_class_073 r
  · exact g32p_supplierGroup02_class_074 r
  · exact g32p_supplierGroup02_class_075 r
  · exact g32p_supplierGroup02_class_076 r
  · exact g32p_supplierGroup02_class_077 r
  · exact g32p_supplierGroup02_class_078 r
  · exact g32p_supplierGroup02_class_079 r
  · exact g32p_supplierGroup02_class_080 r
  · exact g32p_supplierGroup02_class_081 r
  · exact g32p_supplierGroup02_class_082 r
  · exact g32p_supplierGroup02_class_083 r
  · exact g32p_supplierGroup02_class_084 r
  · exact g32p_supplierGroup02_class_085 r
  · exact g32p_supplierGroup02_class_086 r
  · exact g32p_supplierGroup02_class_087 r
  · exact g32p_supplierGroup02_class_088 r
  · exact g32p_supplierGroup02_class_089 r
  · exact g32p_supplierGroup02_class_090 r
  · exact g32p_supplierGroup02_class_091 r
  · exact g32p_supplierGroup02_class_092 r
  · exact g32p_supplierGroup02_class_093 r
  · exact g32p_supplierGroup02_class_094 r
  · exact g32p_supplierGroup02_class_095 r
  · exact g32p_supplierGroup02_class_096 r
  · exact g32p_supplierGroup02_class_097 r
  · exact g32p_supplierGroup02_class_098 r
  · exact g32p_supplierGroup02_class_099 r
  · exact g32p_supplierGroup02_class_100 r
  · exact g32p_supplierGroup02_class_101 r
  · exact g32p_supplierGroup02_class_102 r
  · exact g32p_supplierGroup02_class_103 r
  · exact g32p_supplierGroup02_class_104 r
  · exact g32p_supplierGroup02_class_105 r
  · exact g32p_supplierGroup02_class_106 r
  · exact g32p_supplierGroup02_class_107 r

theorem g32p_supplierGroup02_support_mem (i : Fin 1728) :
    g32p_supplierGroup02_classify i ∈ g32p_supplierGroup02_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup02_classify i ∈ g32p_supplierGroup02_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup02_support_000 r
  · exact g32p_supplierGroup02_support_001 r
  · exact g32p_supplierGroup02_support_002 r
  · exact g32p_supplierGroup02_support_003 r
  · exact g32p_supplierGroup02_support_004 r
  · exact g32p_supplierGroup02_support_005 r
  · exact g32p_supplierGroup02_support_006 r
  · exact g32p_supplierGroup02_support_007 r
  · exact g32p_supplierGroup02_support_008 r
  · exact g32p_supplierGroup02_support_009 r
  · exact g32p_supplierGroup02_support_010 r
  · exact g32p_supplierGroup02_support_011 r
  · exact g32p_supplierGroup02_support_012 r
  · exact g32p_supplierGroup02_support_013 r
  · exact g32p_supplierGroup02_support_014 r
  · exact g32p_supplierGroup02_support_015 r
  · exact g32p_supplierGroup02_support_016 r
  · exact g32p_supplierGroup02_support_017 r
  · exact g32p_supplierGroup02_support_018 r
  · exact g32p_supplierGroup02_support_019 r
  · exact g32p_supplierGroup02_support_020 r
  · exact g32p_supplierGroup02_support_021 r
  · exact g32p_supplierGroup02_support_022 r
  · exact g32p_supplierGroup02_support_023 r
  · exact g32p_supplierGroup02_support_024 r
  · exact g32p_supplierGroup02_support_025 r
  · exact g32p_supplierGroup02_support_026 r
  · exact g32p_supplierGroup02_support_027 r
  · exact g32p_supplierGroup02_support_028 r
  · exact g32p_supplierGroup02_support_029 r
  · exact g32p_supplierGroup02_support_030 r
  · exact g32p_supplierGroup02_support_031 r
  · exact g32p_supplierGroup02_support_032 r
  · exact g32p_supplierGroup02_support_033 r
  · exact g32p_supplierGroup02_support_034 r
  · exact g32p_supplierGroup02_support_035 r
  · exact g32p_supplierGroup02_support_036 r
  · exact g32p_supplierGroup02_support_037 r
  · exact g32p_supplierGroup02_support_038 r
  · exact g32p_supplierGroup02_support_039 r
  · exact g32p_supplierGroup02_support_040 r
  · exact g32p_supplierGroup02_support_041 r
  · exact g32p_supplierGroup02_support_042 r
  · exact g32p_supplierGroup02_support_043 r
  · exact g32p_supplierGroup02_support_044 r
  · exact g32p_supplierGroup02_support_045 r
  · exact g32p_supplierGroup02_support_046 r
  · exact g32p_supplierGroup02_support_047 r
  · exact g32p_supplierGroup02_support_048 r
  · exact g32p_supplierGroup02_support_049 r
  · exact g32p_supplierGroup02_support_050 r
  · exact g32p_supplierGroup02_support_051 r
  · exact g32p_supplierGroup02_support_052 r
  · exact g32p_supplierGroup02_support_053 r
  · exact g32p_supplierGroup02_support_054 r
  · exact g32p_supplierGroup02_support_055 r
  · exact g32p_supplierGroup02_support_056 r
  · exact g32p_supplierGroup02_support_057 r
  · exact g32p_supplierGroup02_support_058 r
  · exact g32p_supplierGroup02_support_059 r
  · exact g32p_supplierGroup02_support_060 r
  · exact g32p_supplierGroup02_support_061 r
  · exact g32p_supplierGroup02_support_062 r
  · exact g32p_supplierGroup02_support_063 r
  · exact g32p_supplierGroup02_support_064 r
  · exact g32p_supplierGroup02_support_065 r
  · exact g32p_supplierGroup02_support_066 r
  · exact g32p_supplierGroup02_support_067 r
  · exact g32p_supplierGroup02_support_068 r
  · exact g32p_supplierGroup02_support_069 r
  · exact g32p_supplierGroup02_support_070 r
  · exact g32p_supplierGroup02_support_071 r
  · exact g32p_supplierGroup02_support_072 r
  · exact g32p_supplierGroup02_support_073 r
  · exact g32p_supplierGroup02_support_074 r
  · exact g32p_supplierGroup02_support_075 r
  · exact g32p_supplierGroup02_support_076 r
  · exact g32p_supplierGroup02_support_077 r
  · exact g32p_supplierGroup02_support_078 r
  · exact g32p_supplierGroup02_support_079 r
  · exact g32p_supplierGroup02_support_080 r
  · exact g32p_supplierGroup02_support_081 r
  · exact g32p_supplierGroup02_support_082 r
  · exact g32p_supplierGroup02_support_083 r
  · exact g32p_supplierGroup02_support_084 r
  · exact g32p_supplierGroup02_support_085 r
  · exact g32p_supplierGroup02_support_086 r
  · exact g32p_supplierGroup02_support_087 r
  · exact g32p_supplierGroup02_support_088 r
  · exact g32p_supplierGroup02_support_089 r
  · exact g32p_supplierGroup02_support_090 r
  · exact g32p_supplierGroup02_support_091 r
  · exact g32p_supplierGroup02_support_092 r
  · exact g32p_supplierGroup02_support_093 r
  · exact g32p_supplierGroup02_support_094 r
  · exact g32p_supplierGroup02_support_095 r
  · exact g32p_supplierGroup02_support_096 r
  · exact g32p_supplierGroup02_support_097 r
  · exact g32p_supplierGroup02_support_098 r
  · exact g32p_supplierGroup02_support_099 r
  · exact g32p_supplierGroup02_support_100 r
  · exact g32p_supplierGroup02_support_101 r
  · exact g32p_supplierGroup02_support_102 r
  · exact g32p_supplierGroup02_support_103 r
  · exact g32p_supplierGroup02_support_104 r
  · exact g32p_supplierGroup02_support_105 r
  · exact g32p_supplierGroup02_support_106 r
  · exact g32p_supplierGroup02_support_107 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row04_supplierClassifier : Fin 1728 → Fin 102 := g32p_supplierGroup02_classify

theorem g32p_row04_groupEquiv_isConj (i : Fin 1728) :
    IsConj (g32p_row04_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row04_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup02_source i).1 (g32p_supplierGroup02_source i).2
  rw [g32p_supplierGroup02_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row04_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup02_matrix i)

def g32p_row04_supplierClass (h : (g32p_recordedSuppliers 3).H) : Fin 102 :=
  g32p_row04_supplierClassifier (g32p_row04_groupEquiv.symm h)

theorem g32p_row04_supplierClass_isConj (h : (g32p_recordedSuppliers 3).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row04_supplierClass h)) := by
  have he : (g32p_row04_groupEquiv (g32p_row04_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 3).H => (a : g32p_G))
      (g32p_row04_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row04_supplierClassifier (g32p_row04_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row04_groupEquiv_isConj (g32p_row04_groupEquiv.symm h)

theorem g32p_row04_supplierClass_iff (h : (g32p_recordedSuppliers 3).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row04_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row04_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row04_supplierClass_isConj h).symm

theorem g32p_row04_supplierClass_mem_support (h : (g32p_recordedSuppliers 3).H) :
    g32p_row04_supplierClass h ∈ g32p_supplierGroup02_support :=
  g32p_supplierGroup02_support_mem (g32p_row04_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_000 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 0 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_000_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 0 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 0 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 0 13 14, g32p_row04_traceSegment_000_0000_0013, g32p_row04_traceSegment_000_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 27 13 14, g32p_row04_traceSegment_000_0027_0013, g32p_row04_traceSegment_000_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 0 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 0 27 27, g32p_row04_traceSegment_000_0000_0027, g32p_row04_traceSegment_000_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 54 13 14, g32p_row04_traceSegment_000_0054_0013, g32p_row04_traceSegment_000_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 81 13 14, g32p_row04_traceSegment_000_0081_0013, g32p_row04_traceSegment_000_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 54 27 27, g32p_row04_traceSegment_000_0054_0027, g32p_row04_traceSegment_000_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 0 54 54, g32p_row04_traceSegment_000_0000_0054, g32p_row04_traceSegment_000_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 108 13 14, g32p_row04_traceSegment_000_0108_0013, g32p_row04_traceSegment_000_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 135 13 14, g32p_row04_traceSegment_000_0135_0013, g32p_row04_traceSegment_000_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 108 27 27, g32p_row04_traceSegment_000_0108_0027, g32p_row04_traceSegment_000_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 162 13 14, g32p_row04_traceSegment_000_0162_0013, g32p_row04_traceSegment_000_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 189 13 14, g32p_row04_traceSegment_000_0189_0013, g32p_row04_traceSegment_000_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 162 27 27, g32p_row04_traceSegment_000_0162_0027, g32p_row04_traceSegment_000_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 108 54 54, g32p_row04_traceSegment_000_0108_0054, g32p_row04_traceSegment_000_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_000 0 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 0 108 108, g32p_row04_traceSegment_000_0000_0108, g32p_row04_traceSegment_000_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 216 13 14, g32p_row04_traceSegment_000_0216_0013, g32p_row04_traceSegment_000_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 243 13 14, g32p_row04_traceSegment_000_0243_0013, g32p_row04_traceSegment_000_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 216 27 27, g32p_row04_traceSegment_000_0216_0027, g32p_row04_traceSegment_000_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 270 13 14, g32p_row04_traceSegment_000_0270_0013, g32p_row04_traceSegment_000_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 297 13 14, g32p_row04_traceSegment_000_0297_0013, g32p_row04_traceSegment_000_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 270 27 27, g32p_row04_traceSegment_000_0270_0027, g32p_row04_traceSegment_000_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 216 54 54, g32p_row04_traceSegment_000_0216_0054, g32p_row04_traceSegment_000_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 324 13 14, g32p_row04_traceSegment_000_0324_0013, g32p_row04_traceSegment_000_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 351 13 14, g32p_row04_traceSegment_000_0351_0013, g32p_row04_traceSegment_000_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 324 27 27, g32p_row04_traceSegment_000_0324_0027, g32p_row04_traceSegment_000_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 378 13 14, g32p_row04_traceSegment_000_0378_0013, g32p_row04_traceSegment_000_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 405 13 14, g32p_row04_traceSegment_000_0405_0013, g32p_row04_traceSegment_000_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 378 27 27, g32p_row04_traceSegment_000_0378_0027, g32p_row04_traceSegment_000_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 324 54 54, g32p_row04_traceSegment_000_0324_0054, g32p_row04_traceSegment_000_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_000 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 216 108 108, g32p_row04_traceSegment_000_0216_0108, g32p_row04_traceSegment_000_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_000 0 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 0 216 216, g32p_row04_traceSegment_000_0000_0216, g32p_row04_traceSegment_000_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 432 13 14, g32p_row04_traceSegment_000_0432_0013, g32p_row04_traceSegment_000_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 459 13 14, g32p_row04_traceSegment_000_0459_0013, g32p_row04_traceSegment_000_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 432 27 27, g32p_row04_traceSegment_000_0432_0027, g32p_row04_traceSegment_000_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 486 13 14, g32p_row04_traceSegment_000_0486_0013, g32p_row04_traceSegment_000_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 513 13 14, g32p_row04_traceSegment_000_0513_0013, g32p_row04_traceSegment_000_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 486 27 27, g32p_row04_traceSegment_000_0486_0027, g32p_row04_traceSegment_000_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 432 54 54, g32p_row04_traceSegment_000_0432_0054, g32p_row04_traceSegment_000_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 540 13 14, g32p_row04_traceSegment_000_0540_0013, g32p_row04_traceSegment_000_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 567 13 14, g32p_row04_traceSegment_000_0567_0013, g32p_row04_traceSegment_000_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 540 27 27, g32p_row04_traceSegment_000_0540_0027, g32p_row04_traceSegment_000_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 594 13 14, g32p_row04_traceSegment_000_0594_0013, g32p_row04_traceSegment_000_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 621 13 14, g32p_row04_traceSegment_000_0621_0013, g32p_row04_traceSegment_000_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 594 27 27, g32p_row04_traceSegment_000_0594_0027, g32p_row04_traceSegment_000_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 540 54 54, g32p_row04_traceSegment_000_0540_0054, g32p_row04_traceSegment_000_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_000 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 432 108 108, g32p_row04_traceSegment_000_0432_0108, g32p_row04_traceSegment_000_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 648 13 14, g32p_row04_traceSegment_000_0648_0013, g32p_row04_traceSegment_000_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 675 13 14, g32p_row04_traceSegment_000_0675_0013, g32p_row04_traceSegment_000_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 648 27 27, g32p_row04_traceSegment_000_0648_0027, g32p_row04_traceSegment_000_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 702 13 14, g32p_row04_traceSegment_000_0702_0013, g32p_row04_traceSegment_000_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 729 13 14, g32p_row04_traceSegment_000_0729_0013, g32p_row04_traceSegment_000_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 702 27 27, g32p_row04_traceSegment_000_0702_0027, g32p_row04_traceSegment_000_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 648 54 54, g32p_row04_traceSegment_000_0648_0054, g32p_row04_traceSegment_000_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 756 13 14, g32p_row04_traceSegment_000_0756_0013, g32p_row04_traceSegment_000_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 783 13 14, g32p_row04_traceSegment_000_0783_0013, g32p_row04_traceSegment_000_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 756 27 27, g32p_row04_traceSegment_000_0756_0027, g32p_row04_traceSegment_000_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 810 13 14, g32p_row04_traceSegment_000_0810_0013, g32p_row04_traceSegment_000_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 837 13 14, g32p_row04_traceSegment_000_0837_0013, g32p_row04_traceSegment_000_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 810 27 27, g32p_row04_traceSegment_000_0810_0027, g32p_row04_traceSegment_000_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 756 54 54, g32p_row04_traceSegment_000_0756_0054, g32p_row04_traceSegment_000_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_000 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 648 108 108, g32p_row04_traceSegment_000_0648_0108, g32p_row04_traceSegment_000_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_000 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 432 216 216, g32p_row04_traceSegment_000_0432_0216, g32p_row04_traceSegment_000_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_000 0 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 0 432 432, g32p_row04_traceSegment_000_0000_0432, g32p_row04_traceSegment_000_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 864 13 14, g32p_row04_traceSegment_000_0864_0013, g32p_row04_traceSegment_000_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 891 13 14, g32p_row04_traceSegment_000_0891_0013, g32p_row04_traceSegment_000_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 864 27 27, g32p_row04_traceSegment_000_0864_0027, g32p_row04_traceSegment_000_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 918 13 14, g32p_row04_traceSegment_000_0918_0013, g32p_row04_traceSegment_000_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 945 13 14, g32p_row04_traceSegment_000_0945_0013, g32p_row04_traceSegment_000_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 918 27 27, g32p_row04_traceSegment_000_0918_0027, g32p_row04_traceSegment_000_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 864 54 54, g32p_row04_traceSegment_000_0864_0054, g32p_row04_traceSegment_000_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 972 13 14, g32p_row04_traceSegment_000_0972_0013, g32p_row04_traceSegment_000_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 999 13 14, g32p_row04_traceSegment_000_0999_0013, g32p_row04_traceSegment_000_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 972 27 27, g32p_row04_traceSegment_000_0972_0027, g32p_row04_traceSegment_000_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1026 13 14, g32p_row04_traceSegment_000_1026_0013, g32p_row04_traceSegment_000_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1053 13 14, g32p_row04_traceSegment_000_1053_0013, g32p_row04_traceSegment_000_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1026 27 27, g32p_row04_traceSegment_000_1026_0027, g32p_row04_traceSegment_000_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 972 54 54, g32p_row04_traceSegment_000_0972_0054, g32p_row04_traceSegment_000_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_000 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 864 108 108, g32p_row04_traceSegment_000_0864_0108, g32p_row04_traceSegment_000_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1080 13 14, g32p_row04_traceSegment_000_1080_0013, g32p_row04_traceSegment_000_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1107 13 14, g32p_row04_traceSegment_000_1107_0013, g32p_row04_traceSegment_000_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1080 27 27, g32p_row04_traceSegment_000_1080_0027, g32p_row04_traceSegment_000_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1134 13 14, g32p_row04_traceSegment_000_1134_0013, g32p_row04_traceSegment_000_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1161 13 14, g32p_row04_traceSegment_000_1161_0013, g32p_row04_traceSegment_000_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1134 27 27, g32p_row04_traceSegment_000_1134_0027, g32p_row04_traceSegment_000_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1080 54 54, g32p_row04_traceSegment_000_1080_0054, g32p_row04_traceSegment_000_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1188 13 14, g32p_row04_traceSegment_000_1188_0013, g32p_row04_traceSegment_000_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1215 13 14, g32p_row04_traceSegment_000_1215_0013, g32p_row04_traceSegment_000_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1188 27 27, g32p_row04_traceSegment_000_1188_0027, g32p_row04_traceSegment_000_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1242 13 14, g32p_row04_traceSegment_000_1242_0013, g32p_row04_traceSegment_000_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1269 13 14, g32p_row04_traceSegment_000_1269_0013, g32p_row04_traceSegment_000_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1242 27 27, g32p_row04_traceSegment_000_1242_0027, g32p_row04_traceSegment_000_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1188 54 54, g32p_row04_traceSegment_000_1188_0054, g32p_row04_traceSegment_000_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_000 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1080 108 108, g32p_row04_traceSegment_000_1080_0108, g32p_row04_traceSegment_000_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_000 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 864 216 216, g32p_row04_traceSegment_000_0864_0216, g32p_row04_traceSegment_000_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1296 13 14, g32p_row04_traceSegment_000_1296_0013, g32p_row04_traceSegment_000_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1323 13 14, g32p_row04_traceSegment_000_1323_0013, g32p_row04_traceSegment_000_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1296 27 27, g32p_row04_traceSegment_000_1296_0027, g32p_row04_traceSegment_000_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1350 13 14, g32p_row04_traceSegment_000_1350_0013, g32p_row04_traceSegment_000_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1377 13 14, g32p_row04_traceSegment_000_1377_0013, g32p_row04_traceSegment_000_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1350 27 27, g32p_row04_traceSegment_000_1350_0027, g32p_row04_traceSegment_000_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1296 54 54, g32p_row04_traceSegment_000_1296_0054, g32p_row04_traceSegment_000_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1404 13 14, g32p_row04_traceSegment_000_1404_0013, g32p_row04_traceSegment_000_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1431 13 14, g32p_row04_traceSegment_000_1431_0013, g32p_row04_traceSegment_000_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1404 27 27, g32p_row04_traceSegment_000_1404_0027, g32p_row04_traceSegment_000_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1458 13 14, g32p_row04_traceSegment_000_1458_0013, g32p_row04_traceSegment_000_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1485 13 14, g32p_row04_traceSegment_000_1485_0013, g32p_row04_traceSegment_000_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1458 27 27, g32p_row04_traceSegment_000_1458_0027, g32p_row04_traceSegment_000_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1404 54 54, g32p_row04_traceSegment_000_1404_0054, g32p_row04_traceSegment_000_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_000 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1296 108 108, g32p_row04_traceSegment_000_1296_0108, g32p_row04_traceSegment_000_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1512 13 14, g32p_row04_traceSegment_000_1512_0013, g32p_row04_traceSegment_000_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1539 13 14, g32p_row04_traceSegment_000_1539_0013, g32p_row04_traceSegment_000_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1512 27 27, g32p_row04_traceSegment_000_1512_0027, g32p_row04_traceSegment_000_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1566 13 14, g32p_row04_traceSegment_000_1566_0013, g32p_row04_traceSegment_000_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1593 13 14, g32p_row04_traceSegment_000_1593_0013, g32p_row04_traceSegment_000_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1566 27 27, g32p_row04_traceSegment_000_1566_0027, g32p_row04_traceSegment_000_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1512 54 54, g32p_row04_traceSegment_000_1512_0054, g32p_row04_traceSegment_000_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1620 13 14, g32p_row04_traceSegment_000_1620_0013, g32p_row04_traceSegment_000_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1647 13 14, g32p_row04_traceSegment_000_1647_0013, g32p_row04_traceSegment_000_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1620 27 27, g32p_row04_traceSegment_000_1620_0027, g32p_row04_traceSegment_000_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1674 13 14, g32p_row04_traceSegment_000_1674_0013, g32p_row04_traceSegment_000_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_000 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_000 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_000_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_000 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1701 13 14, g32p_row04_traceSegment_000_1701_0013, g32p_row04_traceSegment_000_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_000 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1674 27 27, g32p_row04_traceSegment_000_1674_0027, g32p_row04_traceSegment_000_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_000 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1620 54 54, g32p_row04_traceSegment_000_1620_0054, g32p_row04_traceSegment_000_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_000 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1512 108 108, g32p_row04_traceSegment_000_1512_0108, g32p_row04_traceSegment_000_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_000_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_000 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 1296 216 216, g32p_row04_traceSegment_000_1296_0216, g32p_row04_traceSegment_000_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_000 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 864 432 432, g32p_row04_traceSegment_000_0864_0432, g32p_row04_traceSegment_000_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_000_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_000 0 1728 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_000 0 864 864, g32p_row04_traceSegment_000_0000_0864, g32p_row04_traceSegment_000_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 0 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_000_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_001 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 1 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_001_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 13 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 0 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 0 13 14, g32p_row04_traceSegment_001_0000_0013, g32p_row04_traceSegment_001_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 27 13 14, g32p_row04_traceSegment_001_0027_0013, g32p_row04_traceSegment_001_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 0 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 0 27 27, g32p_row04_traceSegment_001_0000_0027, g32p_row04_traceSegment_001_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 54 13 14, g32p_row04_traceSegment_001_0054_0013, g32p_row04_traceSegment_001_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 81 13 14, g32p_row04_traceSegment_001_0081_0013, g32p_row04_traceSegment_001_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 54 27 27, g32p_row04_traceSegment_001_0054_0027, g32p_row04_traceSegment_001_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 0 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 0 54 54, g32p_row04_traceSegment_001_0000_0054, g32p_row04_traceSegment_001_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 108 13 14, g32p_row04_traceSegment_001_0108_0013, g32p_row04_traceSegment_001_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 135 13 14, g32p_row04_traceSegment_001_0135_0013, g32p_row04_traceSegment_001_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 108 27 27, g32p_row04_traceSegment_001_0108_0027, g32p_row04_traceSegment_001_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 175 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 162 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 162 13 14, g32p_row04_traceSegment_001_0162_0013, g32p_row04_traceSegment_001_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 189 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 189 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 189 13 14, g32p_row04_traceSegment_001_0189_0013, g32p_row04_traceSegment_001_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 162 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 162 27 27, g32p_row04_traceSegment_001_0162_0027, g32p_row04_traceSegment_001_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 108 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 108 54 54, g32p_row04_traceSegment_001_0108_0054, g32p_row04_traceSegment_001_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_001 0 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 0 108 108, g32p_row04_traceSegment_001_0000_0108, g32p_row04_traceSegment_001_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 216 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 216 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 216 13 14, g32p_row04_traceSegment_001_0216_0013, g32p_row04_traceSegment_001_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 243 13 14, g32p_row04_traceSegment_001_0243_0013, g32p_row04_traceSegment_001_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 216 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 216 27 27, g32p_row04_traceSegment_001_0216_0027, g32p_row04_traceSegment_001_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 270 13 14, g32p_row04_traceSegment_001_0270_0013, g32p_row04_traceSegment_001_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 297 13 14, g32p_row04_traceSegment_001_0297_0013, g32p_row04_traceSegment_001_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 270 27 27, g32p_row04_traceSegment_001_0270_0027, g32p_row04_traceSegment_001_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 216 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 216 54 54, g32p_row04_traceSegment_001_0216_0054, g32p_row04_traceSegment_001_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 324 13 14, g32p_row04_traceSegment_001_0324_0013, g32p_row04_traceSegment_001_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 351 13 14, g32p_row04_traceSegment_001_0351_0013, g32p_row04_traceSegment_001_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 324 27 27, g32p_row04_traceSegment_001_0324_0027, g32p_row04_traceSegment_001_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 378 13 14, g32p_row04_traceSegment_001_0378_0013, g32p_row04_traceSegment_001_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 405 13 14, g32p_row04_traceSegment_001_0405_0013, g32p_row04_traceSegment_001_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 378 27 27, g32p_row04_traceSegment_001_0378_0027, g32p_row04_traceSegment_001_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 324 54 54, g32p_row04_traceSegment_001_0324_0054, g32p_row04_traceSegment_001_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_001 216 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 216 108 108, g32p_row04_traceSegment_001_0216_0108, g32p_row04_traceSegment_001_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_001 0 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 0 216 216, g32p_row04_traceSegment_001_0000_0216, g32p_row04_traceSegment_001_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 432 13 14, g32p_row04_traceSegment_001_0432_0013, g32p_row04_traceSegment_001_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 459 13 14, g32p_row04_traceSegment_001_0459_0013, g32p_row04_traceSegment_001_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 432 27 27, g32p_row04_traceSegment_001_0432_0027, g32p_row04_traceSegment_001_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 486 13 14, g32p_row04_traceSegment_001_0486_0013, g32p_row04_traceSegment_001_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 513 13 14, g32p_row04_traceSegment_001_0513_0013, g32p_row04_traceSegment_001_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 486 27 27, g32p_row04_traceSegment_001_0486_0027, g32p_row04_traceSegment_001_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 432 54 54, g32p_row04_traceSegment_001_0432_0054, g32p_row04_traceSegment_001_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 540 13 14, g32p_row04_traceSegment_001_0540_0013, g32p_row04_traceSegment_001_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 567 13 14, g32p_row04_traceSegment_001_0567_0013, g32p_row04_traceSegment_001_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 540 27 27, g32p_row04_traceSegment_001_0540_0027, g32p_row04_traceSegment_001_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 594 13 14, g32p_row04_traceSegment_001_0594_0013, g32p_row04_traceSegment_001_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 621 13 14, g32p_row04_traceSegment_001_0621_0013, g32p_row04_traceSegment_001_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 594 27 27, g32p_row04_traceSegment_001_0594_0027, g32p_row04_traceSegment_001_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 540 54 54, g32p_row04_traceSegment_001_0540_0054, g32p_row04_traceSegment_001_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_001 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 432 108 108, g32p_row04_traceSegment_001_0432_0108, g32p_row04_traceSegment_001_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 648 13 14, g32p_row04_traceSegment_001_0648_0013, g32p_row04_traceSegment_001_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 675 13 14, g32p_row04_traceSegment_001_0675_0013, g32p_row04_traceSegment_001_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 648 27 27, g32p_row04_traceSegment_001_0648_0027, g32p_row04_traceSegment_001_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 702 13 14, g32p_row04_traceSegment_001_0702_0013, g32p_row04_traceSegment_001_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 729 13 14, g32p_row04_traceSegment_001_0729_0013, g32p_row04_traceSegment_001_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 702 27 27, g32p_row04_traceSegment_001_0702_0027, g32p_row04_traceSegment_001_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 648 54 54, g32p_row04_traceSegment_001_0648_0054, g32p_row04_traceSegment_001_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 756 13 14, g32p_row04_traceSegment_001_0756_0013, g32p_row04_traceSegment_001_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 783 13 14, g32p_row04_traceSegment_001_0783_0013, g32p_row04_traceSegment_001_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 756 27 27, g32p_row04_traceSegment_001_0756_0027, g32p_row04_traceSegment_001_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 810 13 14, g32p_row04_traceSegment_001_0810_0013, g32p_row04_traceSegment_001_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 837 13 14, g32p_row04_traceSegment_001_0837_0013, g32p_row04_traceSegment_001_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 810 27 27, g32p_row04_traceSegment_001_0810_0027, g32p_row04_traceSegment_001_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 756 54 54, g32p_row04_traceSegment_001_0756_0054, g32p_row04_traceSegment_001_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_001 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 648 108 108, g32p_row04_traceSegment_001_0648_0108, g32p_row04_traceSegment_001_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_001 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 432 216 216, g32p_row04_traceSegment_001_0432_0216, g32p_row04_traceSegment_001_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_001 0 864 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 0 432 432, g32p_row04_traceSegment_001_0000_0432, g32p_row04_traceSegment_001_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 864 13 14, g32p_row04_traceSegment_001_0864_0013, g32p_row04_traceSegment_001_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 891 13 14, g32p_row04_traceSegment_001_0891_0013, g32p_row04_traceSegment_001_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 864 27 27, g32p_row04_traceSegment_001_0864_0027, g32p_row04_traceSegment_001_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 918 13 14, g32p_row04_traceSegment_001_0918_0013, g32p_row04_traceSegment_001_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 945 13 14, g32p_row04_traceSegment_001_0945_0013, g32p_row04_traceSegment_001_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 918 27 27, g32p_row04_traceSegment_001_0918_0027, g32p_row04_traceSegment_001_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 864 54 54, g32p_row04_traceSegment_001_0864_0054, g32p_row04_traceSegment_001_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 972 13 14, g32p_row04_traceSegment_001_0972_0013, g32p_row04_traceSegment_001_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 999 13 14, g32p_row04_traceSegment_001_0999_0013, g32p_row04_traceSegment_001_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 972 27 27, g32p_row04_traceSegment_001_0972_0027, g32p_row04_traceSegment_001_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1026 13 14, g32p_row04_traceSegment_001_1026_0013, g32p_row04_traceSegment_001_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1053 13 14, g32p_row04_traceSegment_001_1053_0013, g32p_row04_traceSegment_001_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1026 27 27, g32p_row04_traceSegment_001_1026_0027, g32p_row04_traceSegment_001_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 972 54 54, g32p_row04_traceSegment_001_0972_0054, g32p_row04_traceSegment_001_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_001 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 864 108 108, g32p_row04_traceSegment_001_0864_0108, g32p_row04_traceSegment_001_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1080 13 14, g32p_row04_traceSegment_001_1080_0013, g32p_row04_traceSegment_001_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1107 13 14, g32p_row04_traceSegment_001_1107_0013, g32p_row04_traceSegment_001_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1080 27 27, g32p_row04_traceSegment_001_1080_0027, g32p_row04_traceSegment_001_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1134 13 14, g32p_row04_traceSegment_001_1134_0013, g32p_row04_traceSegment_001_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1161 13 14, g32p_row04_traceSegment_001_1161_0013, g32p_row04_traceSegment_001_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1134 27 27, g32p_row04_traceSegment_001_1134_0027, g32p_row04_traceSegment_001_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1080 54 54, g32p_row04_traceSegment_001_1080_0054, g32p_row04_traceSegment_001_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1188 13 14, g32p_row04_traceSegment_001_1188_0013, g32p_row04_traceSegment_001_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1215 13 14, g32p_row04_traceSegment_001_1215_0013, g32p_row04_traceSegment_001_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1188 27 27, g32p_row04_traceSegment_001_1188_0027, g32p_row04_traceSegment_001_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1242 13 14, g32p_row04_traceSegment_001_1242_0013, g32p_row04_traceSegment_001_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1269 13 14, g32p_row04_traceSegment_001_1269_0013, g32p_row04_traceSegment_001_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1242 27 27, g32p_row04_traceSegment_001_1242_0027, g32p_row04_traceSegment_001_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1188 54 54, g32p_row04_traceSegment_001_1188_0054, g32p_row04_traceSegment_001_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_001 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1080 108 108, g32p_row04_traceSegment_001_1080_0108, g32p_row04_traceSegment_001_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_001 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 864 216 216, g32p_row04_traceSegment_001_0864_0216, g32p_row04_traceSegment_001_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1296 13 14, g32p_row04_traceSegment_001_1296_0013, g32p_row04_traceSegment_001_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1323 13 14, g32p_row04_traceSegment_001_1323_0013, g32p_row04_traceSegment_001_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1296 27 27, g32p_row04_traceSegment_001_1296_0027, g32p_row04_traceSegment_001_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1350 13 14, g32p_row04_traceSegment_001_1350_0013, g32p_row04_traceSegment_001_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1377 13 14, g32p_row04_traceSegment_001_1377_0013, g32p_row04_traceSegment_001_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1350 27 27, g32p_row04_traceSegment_001_1350_0027, g32p_row04_traceSegment_001_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1296 54 54, g32p_row04_traceSegment_001_1296_0054, g32p_row04_traceSegment_001_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1404 13 14, g32p_row04_traceSegment_001_1404_0013, g32p_row04_traceSegment_001_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1431 13 14, g32p_row04_traceSegment_001_1431_0013, g32p_row04_traceSegment_001_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1404 27 27, g32p_row04_traceSegment_001_1404_0027, g32p_row04_traceSegment_001_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1458 13 14, g32p_row04_traceSegment_001_1458_0013, g32p_row04_traceSegment_001_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1485 13 14, g32p_row04_traceSegment_001_1485_0013, g32p_row04_traceSegment_001_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1458 27 27, g32p_row04_traceSegment_001_1458_0027, g32p_row04_traceSegment_001_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1404 54 54, g32p_row04_traceSegment_001_1404_0054, g32p_row04_traceSegment_001_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_001 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1296 108 108, g32p_row04_traceSegment_001_1296_0108, g32p_row04_traceSegment_001_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1512 13 14, g32p_row04_traceSegment_001_1512_0013, g32p_row04_traceSegment_001_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1539 13 14, g32p_row04_traceSegment_001_1539_0013, g32p_row04_traceSegment_001_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1512 27 27, g32p_row04_traceSegment_001_1512_0027, g32p_row04_traceSegment_001_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1566 13 14, g32p_row04_traceSegment_001_1566_0013, g32p_row04_traceSegment_001_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1593 13 14, g32p_row04_traceSegment_001_1593_0013, g32p_row04_traceSegment_001_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1566 27 27, g32p_row04_traceSegment_001_1566_0027, g32p_row04_traceSegment_001_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1512 54 54, g32p_row04_traceSegment_001_1512_0054, g32p_row04_traceSegment_001_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1620 13 14, g32p_row04_traceSegment_001_1620_0013, g32p_row04_traceSegment_001_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1647 13 14, g32p_row04_traceSegment_001_1647_0013, g32p_row04_traceSegment_001_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1620 27 27, g32p_row04_traceSegment_001_1620_0027, g32p_row04_traceSegment_001_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1674 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1674 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1674 13 14, g32p_row04_traceSegment_001_1674_0013, g32p_row04_traceSegment_001_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_001 1701 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_001 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_001_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_001 1701 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1701 13 14, g32p_row04_traceSegment_001_1701_0013, g32p_row04_traceSegment_001_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_001 1674 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1674 27 27, g32p_row04_traceSegment_001_1674_0027, g32p_row04_traceSegment_001_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_001 1620 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1620 54 54, g32p_row04_traceSegment_001_1620_0054, g32p_row04_traceSegment_001_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_001 1512 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1512 108 108, g32p_row04_traceSegment_001_1512_0108, g32p_row04_traceSegment_001_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_001_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_001 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 1296 216 216, g32p_row04_traceSegment_001_1296_0216, g32p_row04_traceSegment_001_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_001 864 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 864 432 432, g32p_row04_traceSegment_001_0864_0432, g32p_row04_traceSegment_001_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_001_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_001 0 1728 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_001 0 864 864, g32p_row04_traceSegment_001_0000_0864, g32p_row04_traceSegment_001_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 1 = [4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_001_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_002 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 2 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_002_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 13 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 0 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 0 13 14, g32p_row04_traceSegment_002_0000_0013, g32p_row04_traceSegment_002_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 27 13 14, g32p_row04_traceSegment_002_0027_0013, g32p_row04_traceSegment_002_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 0 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 0 27 27, g32p_row04_traceSegment_002_0000_0027, g32p_row04_traceSegment_002_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 54 13 14, g32p_row04_traceSegment_002_0054_0013, g32p_row04_traceSegment_002_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 81 13 14, g32p_row04_traceSegment_002_0081_0013, g32p_row04_traceSegment_002_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 54 27 27, g32p_row04_traceSegment_002_0054_0027, g32p_row04_traceSegment_002_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 0 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 0 54 54, g32p_row04_traceSegment_002_0000_0054, g32p_row04_traceSegment_002_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 108 13 14, g32p_row04_traceSegment_002_0108_0013, g32p_row04_traceSegment_002_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 135 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 148 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 135 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 135 13 14, g32p_row04_traceSegment_002_0135_0013, g32p_row04_traceSegment_002_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 108 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 108 27 27, g32p_row04_traceSegment_002_0108_0027, g32p_row04_traceSegment_002_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 162 13 14, g32p_row04_traceSegment_002_0162_0013, g32p_row04_traceSegment_002_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 189 13 14, g32p_row04_traceSegment_002_0189_0013, g32p_row04_traceSegment_002_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 162 27 27, g32p_row04_traceSegment_002_0162_0027, g32p_row04_traceSegment_002_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 108 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 108 54 54, g32p_row04_traceSegment_002_0108_0054, g32p_row04_traceSegment_002_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_002 0 216 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 0 108 108, g32p_row04_traceSegment_002_0000_0108, g32p_row04_traceSegment_002_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 216 13 14, g32p_row04_traceSegment_002_0216_0013, g32p_row04_traceSegment_002_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 243 13 14, g32p_row04_traceSegment_002_0243_0013, g32p_row04_traceSegment_002_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 216 27 27, g32p_row04_traceSegment_002_0216_0027, g32p_row04_traceSegment_002_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 270 13 14, g32p_row04_traceSegment_002_0270_0013, g32p_row04_traceSegment_002_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 297 13 14, g32p_row04_traceSegment_002_0297_0013, g32p_row04_traceSegment_002_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 270 27 27, g32p_row04_traceSegment_002_0270_0027, g32p_row04_traceSegment_002_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 216 54 54, g32p_row04_traceSegment_002_0216_0054, g32p_row04_traceSegment_002_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 324 13 14, g32p_row04_traceSegment_002_0324_0013, g32p_row04_traceSegment_002_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 351 13 14, g32p_row04_traceSegment_002_0351_0013, g32p_row04_traceSegment_002_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 324 27 27, g32p_row04_traceSegment_002_0324_0027, g32p_row04_traceSegment_002_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 378 13 14, g32p_row04_traceSegment_002_0378_0013, g32p_row04_traceSegment_002_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 405 13 14, g32p_row04_traceSegment_002_0405_0013, g32p_row04_traceSegment_002_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 378 27 27, g32p_row04_traceSegment_002_0378_0027, g32p_row04_traceSegment_002_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 324 54 54, g32p_row04_traceSegment_002_0324_0054, g32p_row04_traceSegment_002_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_002 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 216 108 108, g32p_row04_traceSegment_002_0216_0108, g32p_row04_traceSegment_002_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_002 0 432 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 0 216 216, g32p_row04_traceSegment_002_0000_0216, g32p_row04_traceSegment_002_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 432 13 14, g32p_row04_traceSegment_002_0432_0013, g32p_row04_traceSegment_002_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 459 13 14, g32p_row04_traceSegment_002_0459_0013, g32p_row04_traceSegment_002_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 432 27 27, g32p_row04_traceSegment_002_0432_0027, g32p_row04_traceSegment_002_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 486 13 14, g32p_row04_traceSegment_002_0486_0013, g32p_row04_traceSegment_002_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 513 13 14, g32p_row04_traceSegment_002_0513_0013, g32p_row04_traceSegment_002_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 486 27 27, g32p_row04_traceSegment_002_0486_0027, g32p_row04_traceSegment_002_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 432 54 54, g32p_row04_traceSegment_002_0432_0054, g32p_row04_traceSegment_002_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 540 13 14, g32p_row04_traceSegment_002_0540_0013, g32p_row04_traceSegment_002_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 567 13 14, g32p_row04_traceSegment_002_0567_0013, g32p_row04_traceSegment_002_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 540 27 27, g32p_row04_traceSegment_002_0540_0027, g32p_row04_traceSegment_002_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 594 13 14, g32p_row04_traceSegment_002_0594_0013, g32p_row04_traceSegment_002_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 621 13 14, g32p_row04_traceSegment_002_0621_0013, g32p_row04_traceSegment_002_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 594 27 27, g32p_row04_traceSegment_002_0594_0027, g32p_row04_traceSegment_002_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 540 54 54, g32p_row04_traceSegment_002_0540_0054, g32p_row04_traceSegment_002_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_002 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 432 108 108, g32p_row04_traceSegment_002_0432_0108, g32p_row04_traceSegment_002_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 648 13 14, g32p_row04_traceSegment_002_0648_0013, g32p_row04_traceSegment_002_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 675 13 14, g32p_row04_traceSegment_002_0675_0013, g32p_row04_traceSegment_002_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 648 27 27, g32p_row04_traceSegment_002_0648_0027, g32p_row04_traceSegment_002_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 702 13 14, g32p_row04_traceSegment_002_0702_0013, g32p_row04_traceSegment_002_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 729 13 14, g32p_row04_traceSegment_002_0729_0013, g32p_row04_traceSegment_002_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 702 27 27, g32p_row04_traceSegment_002_0702_0027, g32p_row04_traceSegment_002_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 648 54 54, g32p_row04_traceSegment_002_0648_0054, g32p_row04_traceSegment_002_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 756 13 14, g32p_row04_traceSegment_002_0756_0013, g32p_row04_traceSegment_002_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 783 13 14, g32p_row04_traceSegment_002_0783_0013, g32p_row04_traceSegment_002_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 756 27 27, g32p_row04_traceSegment_002_0756_0027, g32p_row04_traceSegment_002_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 810 13 14, g32p_row04_traceSegment_002_0810_0013, g32p_row04_traceSegment_002_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 837 13 14, g32p_row04_traceSegment_002_0837_0013, g32p_row04_traceSegment_002_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 810 27 27, g32p_row04_traceSegment_002_0810_0027, g32p_row04_traceSegment_002_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 756 54 54, g32p_row04_traceSegment_002_0756_0054, g32p_row04_traceSegment_002_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_002 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 648 108 108, g32p_row04_traceSegment_002_0648_0108, g32p_row04_traceSegment_002_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_002 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 432 216 216, g32p_row04_traceSegment_002_0432_0216, g32p_row04_traceSegment_002_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_002 0 864 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 0 432 432, g32p_row04_traceSegment_002_0000_0432, g32p_row04_traceSegment_002_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 864 13 14, g32p_row04_traceSegment_002_0864_0013, g32p_row04_traceSegment_002_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 891 13 14, g32p_row04_traceSegment_002_0891_0013, g32p_row04_traceSegment_002_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 864 27 27, g32p_row04_traceSegment_002_0864_0027, g32p_row04_traceSegment_002_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 931 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 918 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 918 13 14, g32p_row04_traceSegment_002_0918_0013, g32p_row04_traceSegment_002_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 945 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 945 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 945 13 14, g32p_row04_traceSegment_002_0945_0013, g32p_row04_traceSegment_002_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 918 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 918 27 27, g32p_row04_traceSegment_002_0918_0027, g32p_row04_traceSegment_002_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 864 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 864 54 54, g32p_row04_traceSegment_002_0864_0054, g32p_row04_traceSegment_002_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 972 13 14, g32p_row04_traceSegment_002_0972_0013, g32p_row04_traceSegment_002_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1012 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 999 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 999 13 14, g32p_row04_traceSegment_002_0999_0013, g32p_row04_traceSegment_002_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 972 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 972 27 27, g32p_row04_traceSegment_002_0972_0027, g32p_row04_traceSegment_002_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1026 13 14, g32p_row04_traceSegment_002_1026_0013, g32p_row04_traceSegment_002_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1053 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1053 13 14, g32p_row04_traceSegment_002_1053_0013, g32p_row04_traceSegment_002_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1026 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1026 27 27, g32p_row04_traceSegment_002_1026_0027, g32p_row04_traceSegment_002_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 972 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 972 54 54, g32p_row04_traceSegment_002_0972_0054, g32p_row04_traceSegment_002_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_002 864 216 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 864 108 108, g32p_row04_traceSegment_002_0864_0108, g32p_row04_traceSegment_002_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1080 13 14, g32p_row04_traceSegment_002_1080_0013, g32p_row04_traceSegment_002_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1120 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1107 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1107 13 14, g32p_row04_traceSegment_002_1107_0013, g32p_row04_traceSegment_002_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1080 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1080 27 27, g32p_row04_traceSegment_002_1080_0027, g32p_row04_traceSegment_002_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1134 13 14, g32p_row04_traceSegment_002_1134_0013, g32p_row04_traceSegment_002_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1161 13 14, g32p_row04_traceSegment_002_1161_0013, g32p_row04_traceSegment_002_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1134 27 27, g32p_row04_traceSegment_002_1134_0027, g32p_row04_traceSegment_002_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 1080 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1080 54 54, g32p_row04_traceSegment_002_1080_0054, g32p_row04_traceSegment_002_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1188 13 14, g32p_row04_traceSegment_002_1188_0013, g32p_row04_traceSegment_002_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1215 13 14, g32p_row04_traceSegment_002_1215_0013, g32p_row04_traceSegment_002_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1188 27 27, g32p_row04_traceSegment_002_1188_0027, g32p_row04_traceSegment_002_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1242 13 14, g32p_row04_traceSegment_002_1242_0013, g32p_row04_traceSegment_002_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1269 13 14, g32p_row04_traceSegment_002_1269_0013, g32p_row04_traceSegment_002_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1242 27 27, g32p_row04_traceSegment_002_1242_0027, g32p_row04_traceSegment_002_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1188 54 54, g32p_row04_traceSegment_002_1188_0054, g32p_row04_traceSegment_002_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_002 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1080 108 108, g32p_row04_traceSegment_002_1080_0108, g32p_row04_traceSegment_002_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_002 864 432 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 864 216 216, g32p_row04_traceSegment_002_0864_0216, g32p_row04_traceSegment_002_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1296 13 14, g32p_row04_traceSegment_002_1296_0013, g32p_row04_traceSegment_002_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1323 13 14, g32p_row04_traceSegment_002_1323_0013, g32p_row04_traceSegment_002_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1296 27 27, g32p_row04_traceSegment_002_1296_0027, g32p_row04_traceSegment_002_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1350 13 14, g32p_row04_traceSegment_002_1350_0013, g32p_row04_traceSegment_002_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1377 13 14, g32p_row04_traceSegment_002_1377_0013, g32p_row04_traceSegment_002_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1350 27 27, g32p_row04_traceSegment_002_1350_0027, g32p_row04_traceSegment_002_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1296 54 54, g32p_row04_traceSegment_002_1296_0054, g32p_row04_traceSegment_002_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1404 13 14, g32p_row04_traceSegment_002_1404_0013, g32p_row04_traceSegment_002_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1431 13 14, g32p_row04_traceSegment_002_1431_0013, g32p_row04_traceSegment_002_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1404 27 27, g32p_row04_traceSegment_002_1404_0027, g32p_row04_traceSegment_002_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1458 13 14, g32p_row04_traceSegment_002_1458_0013, g32p_row04_traceSegment_002_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1485 13 14, g32p_row04_traceSegment_002_1485_0013, g32p_row04_traceSegment_002_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1458 27 27, g32p_row04_traceSegment_002_1458_0027, g32p_row04_traceSegment_002_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1404 54 54, g32p_row04_traceSegment_002_1404_0054, g32p_row04_traceSegment_002_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_002 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1296 108 108, g32p_row04_traceSegment_002_1296_0108, g32p_row04_traceSegment_002_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1512 13 14, g32p_row04_traceSegment_002_1512_0013, g32p_row04_traceSegment_002_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1539 13 14, g32p_row04_traceSegment_002_1539_0013, g32p_row04_traceSegment_002_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1512 27 27, g32p_row04_traceSegment_002_1512_0027, g32p_row04_traceSegment_002_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1566 13 14, g32p_row04_traceSegment_002_1566_0013, g32p_row04_traceSegment_002_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1593 13 14, g32p_row04_traceSegment_002_1593_0013, g32p_row04_traceSegment_002_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1566 27 27, g32p_row04_traceSegment_002_1566_0027, g32p_row04_traceSegment_002_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1512 54 54, g32p_row04_traceSegment_002_1512_0054, g32p_row04_traceSegment_002_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1620 13 14, g32p_row04_traceSegment_002_1620_0013, g32p_row04_traceSegment_002_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1647 13 14, g32p_row04_traceSegment_002_1647_0013, g32p_row04_traceSegment_002_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1620 27 27, g32p_row04_traceSegment_002_1620_0027, g32p_row04_traceSegment_002_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1674 13 14, g32p_row04_traceSegment_002_1674_0013, g32p_row04_traceSegment_002_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_002 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_002 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_002_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_002 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1701 13 14, g32p_row04_traceSegment_002_1701_0013, g32p_row04_traceSegment_002_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_002 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1674 27 27, g32p_row04_traceSegment_002_1674_0027, g32p_row04_traceSegment_002_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_002 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1620 54 54, g32p_row04_traceSegment_002_1620_0054, g32p_row04_traceSegment_002_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_002 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1512 108 108, g32p_row04_traceSegment_002_1512_0108, g32p_row04_traceSegment_002_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_002_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_002 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 1296 216 216, g32p_row04_traceSegment_002_1296_0216, g32p_row04_traceSegment_002_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_002 864 864 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 864 432 432, g32p_row04_traceSegment_002_0864_0432, g32p_row04_traceSegment_002_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_002_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_002 0 1728 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_002 0 864 864, g32p_row04_traceSegment_002_0000_0864, g32p_row04_traceSegment_002_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 2 = [4, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_002_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_003 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 3 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_003_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 0 13 14, g32p_row04_traceSegment_003_0000_0013, g32p_row04_traceSegment_003_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 27 13 14, g32p_row04_traceSegment_003_0027_0013, g32p_row04_traceSegment_003_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 0 27 27, g32p_row04_traceSegment_003_0000_0027, g32p_row04_traceSegment_003_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 54 13 14, g32p_row04_traceSegment_003_0054_0013, g32p_row04_traceSegment_003_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 81 13 14, g32p_row04_traceSegment_003_0081_0013, g32p_row04_traceSegment_003_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 54 27 27, g32p_row04_traceSegment_003_0054_0027, g32p_row04_traceSegment_003_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 0 54 54, g32p_row04_traceSegment_003_0000_0054, g32p_row04_traceSegment_003_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 108 13 14, g32p_row04_traceSegment_003_0108_0013, g32p_row04_traceSegment_003_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 135 13 14, g32p_row04_traceSegment_003_0135_0013, g32p_row04_traceSegment_003_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 108 27 27, g32p_row04_traceSegment_003_0108_0027, g32p_row04_traceSegment_003_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 175 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 162 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 162 13 14, g32p_row04_traceSegment_003_0162_0013, g32p_row04_traceSegment_003_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 189 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 189 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 189 13 14, g32p_row04_traceSegment_003_0189_0013, g32p_row04_traceSegment_003_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 162 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 162 27 27, g32p_row04_traceSegment_003_0162_0027, g32p_row04_traceSegment_003_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 108 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 108 54 54, g32p_row04_traceSegment_003_0108_0054, g32p_row04_traceSegment_003_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_003 0 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 0 108 108, g32p_row04_traceSegment_003_0000_0108, g32p_row04_traceSegment_003_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 216 13 14, g32p_row04_traceSegment_003_0216_0013, g32p_row04_traceSegment_003_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 243 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 243 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 243 13 14, g32p_row04_traceSegment_003_0243_0013, g32p_row04_traceSegment_003_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 216 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 216 27 27, g32p_row04_traceSegment_003_0216_0027, g32p_row04_traceSegment_003_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 270 13 14, g32p_row04_traceSegment_003_0270_0013, g32p_row04_traceSegment_003_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 297 13 14, g32p_row04_traceSegment_003_0297_0013, g32p_row04_traceSegment_003_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 270 27 27, g32p_row04_traceSegment_003_0270_0027, g32p_row04_traceSegment_003_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 216 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 216 54 54, g32p_row04_traceSegment_003_0216_0054, g32p_row04_traceSegment_003_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 324 13 14, g32p_row04_traceSegment_003_0324_0013, g32p_row04_traceSegment_003_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 351 13 14, g32p_row04_traceSegment_003_0351_0013, g32p_row04_traceSegment_003_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 324 27 27, g32p_row04_traceSegment_003_0324_0027, g32p_row04_traceSegment_003_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 378 13 14, g32p_row04_traceSegment_003_0378_0013, g32p_row04_traceSegment_003_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 405 13 14, g32p_row04_traceSegment_003_0405_0013, g32p_row04_traceSegment_003_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 378 27 27, g32p_row04_traceSegment_003_0378_0027, g32p_row04_traceSegment_003_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 324 54 54, g32p_row04_traceSegment_003_0324_0054, g32p_row04_traceSegment_003_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_003 216 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 216 108 108, g32p_row04_traceSegment_003_0216_0108, g32p_row04_traceSegment_003_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_003 0 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 0 216 216, g32p_row04_traceSegment_003_0000_0216, g32p_row04_traceSegment_003_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 432 13 14, g32p_row04_traceSegment_003_0432_0013, g32p_row04_traceSegment_003_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 459 13 14, g32p_row04_traceSegment_003_0459_0013, g32p_row04_traceSegment_003_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 432 27 27, g32p_row04_traceSegment_003_0432_0027, g32p_row04_traceSegment_003_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 486 13 14, g32p_row04_traceSegment_003_0486_0013, g32p_row04_traceSegment_003_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 513 13 14, g32p_row04_traceSegment_003_0513_0013, g32p_row04_traceSegment_003_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 486 27 27, g32p_row04_traceSegment_003_0486_0027, g32p_row04_traceSegment_003_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 432 54 54, g32p_row04_traceSegment_003_0432_0054, g32p_row04_traceSegment_003_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 540 13 14, g32p_row04_traceSegment_003_0540_0013, g32p_row04_traceSegment_003_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 567 13 14, g32p_row04_traceSegment_003_0567_0013, g32p_row04_traceSegment_003_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 540 27 27, g32p_row04_traceSegment_003_0540_0027, g32p_row04_traceSegment_003_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 594 13 14, g32p_row04_traceSegment_003_0594_0013, g32p_row04_traceSegment_003_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 621 13 14, g32p_row04_traceSegment_003_0621_0013, g32p_row04_traceSegment_003_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 594 27 27, g32p_row04_traceSegment_003_0594_0027, g32p_row04_traceSegment_003_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 540 54 54, g32p_row04_traceSegment_003_0540_0054, g32p_row04_traceSegment_003_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_003 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 432 108 108, g32p_row04_traceSegment_003_0432_0108, g32p_row04_traceSegment_003_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 648 13 14, g32p_row04_traceSegment_003_0648_0013, g32p_row04_traceSegment_003_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 675 13 14, g32p_row04_traceSegment_003_0675_0013, g32p_row04_traceSegment_003_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 648 27 27, g32p_row04_traceSegment_003_0648_0027, g32p_row04_traceSegment_003_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 702 13 14, g32p_row04_traceSegment_003_0702_0013, g32p_row04_traceSegment_003_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 729 13 14, g32p_row04_traceSegment_003_0729_0013, g32p_row04_traceSegment_003_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 702 27 27, g32p_row04_traceSegment_003_0702_0027, g32p_row04_traceSegment_003_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 648 54 54, g32p_row04_traceSegment_003_0648_0054, g32p_row04_traceSegment_003_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 756 13 14, g32p_row04_traceSegment_003_0756_0013, g32p_row04_traceSegment_003_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 783 13 14, g32p_row04_traceSegment_003_0783_0013, g32p_row04_traceSegment_003_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 756 27 27, g32p_row04_traceSegment_003_0756_0027, g32p_row04_traceSegment_003_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 810 13 14, g32p_row04_traceSegment_003_0810_0013, g32p_row04_traceSegment_003_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 837 13 14, g32p_row04_traceSegment_003_0837_0013, g32p_row04_traceSegment_003_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 810 27 27, g32p_row04_traceSegment_003_0810_0027, g32p_row04_traceSegment_003_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 756 54 54, g32p_row04_traceSegment_003_0756_0054, g32p_row04_traceSegment_003_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_003 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 648 108 108, g32p_row04_traceSegment_003_0648_0108, g32p_row04_traceSegment_003_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_003 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 432 216 216, g32p_row04_traceSegment_003_0432_0216, g32p_row04_traceSegment_003_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_003 0 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 0 432 432, g32p_row04_traceSegment_003_0000_0432, g32p_row04_traceSegment_003_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 864 13 14, g32p_row04_traceSegment_003_0864_0013, g32p_row04_traceSegment_003_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 891 13 14, g32p_row04_traceSegment_003_0891_0013, g32p_row04_traceSegment_003_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 864 27 27, g32p_row04_traceSegment_003_0864_0027, g32p_row04_traceSegment_003_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 918 13 14, g32p_row04_traceSegment_003_0918_0013, g32p_row04_traceSegment_003_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 945 13 14, g32p_row04_traceSegment_003_0945_0013, g32p_row04_traceSegment_003_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 918 27 27, g32p_row04_traceSegment_003_0918_0027, g32p_row04_traceSegment_003_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 864 54 54, g32p_row04_traceSegment_003_0864_0054, g32p_row04_traceSegment_003_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 972 13 14, g32p_row04_traceSegment_003_0972_0013, g32p_row04_traceSegment_003_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 999 13 14, g32p_row04_traceSegment_003_0999_0013, g32p_row04_traceSegment_003_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 972 27 27, g32p_row04_traceSegment_003_0972_0027, g32p_row04_traceSegment_003_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1026 13 14, g32p_row04_traceSegment_003_1026_0013, g32p_row04_traceSegment_003_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1053 13 14, g32p_row04_traceSegment_003_1053_0013, g32p_row04_traceSegment_003_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1026 27 27, g32p_row04_traceSegment_003_1026_0027, g32p_row04_traceSegment_003_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 972 54 54, g32p_row04_traceSegment_003_0972_0054, g32p_row04_traceSegment_003_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_003 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 864 108 108, g32p_row04_traceSegment_003_0864_0108, g32p_row04_traceSegment_003_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1080 13 14, g32p_row04_traceSegment_003_1080_0013, g32p_row04_traceSegment_003_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1107 13 14, g32p_row04_traceSegment_003_1107_0013, g32p_row04_traceSegment_003_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1080 27 27, g32p_row04_traceSegment_003_1080_0027, g32p_row04_traceSegment_003_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1134 13 14, g32p_row04_traceSegment_003_1134_0013, g32p_row04_traceSegment_003_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1161 13 14, g32p_row04_traceSegment_003_1161_0013, g32p_row04_traceSegment_003_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1134 27 27, g32p_row04_traceSegment_003_1134_0027, g32p_row04_traceSegment_003_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1080 54 54, g32p_row04_traceSegment_003_1080_0054, g32p_row04_traceSegment_003_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1188 13 14, g32p_row04_traceSegment_003_1188_0013, g32p_row04_traceSegment_003_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1215 13 14, g32p_row04_traceSegment_003_1215_0013, g32p_row04_traceSegment_003_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1188 27 27, g32p_row04_traceSegment_003_1188_0027, g32p_row04_traceSegment_003_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1242 13 14, g32p_row04_traceSegment_003_1242_0013, g32p_row04_traceSegment_003_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1269 13 14, g32p_row04_traceSegment_003_1269_0013, g32p_row04_traceSegment_003_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1242 27 27, g32p_row04_traceSegment_003_1242_0027, g32p_row04_traceSegment_003_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1188 54 54, g32p_row04_traceSegment_003_1188_0054, g32p_row04_traceSegment_003_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_003 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1080 108 108, g32p_row04_traceSegment_003_1080_0108, g32p_row04_traceSegment_003_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_003 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 864 216 216, g32p_row04_traceSegment_003_0864_0216, g32p_row04_traceSegment_003_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1296 13 14, g32p_row04_traceSegment_003_1296_0013, g32p_row04_traceSegment_003_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1323 13 14, g32p_row04_traceSegment_003_1323_0013, g32p_row04_traceSegment_003_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1296 27 27, g32p_row04_traceSegment_003_1296_0027, g32p_row04_traceSegment_003_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1350 13 14, g32p_row04_traceSegment_003_1350_0013, g32p_row04_traceSegment_003_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1377 13 14, g32p_row04_traceSegment_003_1377_0013, g32p_row04_traceSegment_003_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1350 27 27, g32p_row04_traceSegment_003_1350_0027, g32p_row04_traceSegment_003_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1296 54 54, g32p_row04_traceSegment_003_1296_0054, g32p_row04_traceSegment_003_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1404 13 14, g32p_row04_traceSegment_003_1404_0013, g32p_row04_traceSegment_003_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1431 13 14, g32p_row04_traceSegment_003_1431_0013, g32p_row04_traceSegment_003_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1404 27 27, g32p_row04_traceSegment_003_1404_0027, g32p_row04_traceSegment_003_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1458 13 14, g32p_row04_traceSegment_003_1458_0013, g32p_row04_traceSegment_003_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1485 13 14, g32p_row04_traceSegment_003_1485_0013, g32p_row04_traceSegment_003_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1458 27 27, g32p_row04_traceSegment_003_1458_0027, g32p_row04_traceSegment_003_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1404 54 54, g32p_row04_traceSegment_003_1404_0054, g32p_row04_traceSegment_003_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_003 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1296 108 108, g32p_row04_traceSegment_003_1296_0108, g32p_row04_traceSegment_003_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1512 13 14, g32p_row04_traceSegment_003_1512_0013, g32p_row04_traceSegment_003_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1539 13 14, g32p_row04_traceSegment_003_1539_0013, g32p_row04_traceSegment_003_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1512 27 27, g32p_row04_traceSegment_003_1512_0027, g32p_row04_traceSegment_003_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1566 13 14, g32p_row04_traceSegment_003_1566_0013, g32p_row04_traceSegment_003_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1593 13 14, g32p_row04_traceSegment_003_1593_0013, g32p_row04_traceSegment_003_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1566 27 27, g32p_row04_traceSegment_003_1566_0027, g32p_row04_traceSegment_003_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1512 54 54, g32p_row04_traceSegment_003_1512_0054, g32p_row04_traceSegment_003_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1620 13 14, g32p_row04_traceSegment_003_1620_0013, g32p_row04_traceSegment_003_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1647 13 14, g32p_row04_traceSegment_003_1647_0013, g32p_row04_traceSegment_003_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1620 27 27, g32p_row04_traceSegment_003_1620_0027, g32p_row04_traceSegment_003_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1687 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1674 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1674 13 14, g32p_row04_traceSegment_003_1674_0013, g32p_row04_traceSegment_003_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_003 1701 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_003 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_003_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_003 1701 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1701 13 14, g32p_row04_traceSegment_003_1701_0013, g32p_row04_traceSegment_003_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_003 1674 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1674 27 27, g32p_row04_traceSegment_003_1674_0027, g32p_row04_traceSegment_003_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_003 1620 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1620 54 54, g32p_row04_traceSegment_003_1620_0054, g32p_row04_traceSegment_003_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_003 1512 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1512 108 108, g32p_row04_traceSegment_003_1512_0108, g32p_row04_traceSegment_003_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_003_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_003 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 1296 216 216, g32p_row04_traceSegment_003_1296_0216, g32p_row04_traceSegment_003_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_003 864 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 864 432 432, g32p_row04_traceSegment_003_0864_0432, g32p_row04_traceSegment_003_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_003_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_003 0 1728 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_003 0 864 864, g32p_row04_traceSegment_003_0000_0864, g32p_row04_traceSegment_003_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 3 = [4, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_003_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_004 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 4 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_004_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 0 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 0 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 0 13 14, g32p_row04_traceSegment_004_0000_0013, g32p_row04_traceSegment_004_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 27 13 14, g32p_row04_traceSegment_004_0027_0013, g32p_row04_traceSegment_004_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 0 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 0 27 27, g32p_row04_traceSegment_004_0000_0027, g32p_row04_traceSegment_004_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 67 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 54 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 54 13 14, g32p_row04_traceSegment_004_0054_0013, g32p_row04_traceSegment_004_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 81 13 14, g32p_row04_traceSegment_004_0081_0013, g32p_row04_traceSegment_004_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 54 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 54 27 27, g32p_row04_traceSegment_004_0054_0027, g32p_row04_traceSegment_004_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 0 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 0 54 54, g32p_row04_traceSegment_004_0000_0054, g32p_row04_traceSegment_004_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 108 13 14, g32p_row04_traceSegment_004_0108_0013, g32p_row04_traceSegment_004_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 135 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 135 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 135 13 14, g32p_row04_traceSegment_004_0135_0013, g32p_row04_traceSegment_004_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 108 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 108 27 27, g32p_row04_traceSegment_004_0108_0027, g32p_row04_traceSegment_004_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 162 13 14, g32p_row04_traceSegment_004_0162_0013, g32p_row04_traceSegment_004_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 202 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 189 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 189 13 14, g32p_row04_traceSegment_004_0189_0013, g32p_row04_traceSegment_004_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 162 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 162 27 27, g32p_row04_traceSegment_004_0162_0027, g32p_row04_traceSegment_004_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 108 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 108 54 54, g32p_row04_traceSegment_004_0108_0054, g32p_row04_traceSegment_004_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_004 0 216 = [4, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 0 108 108, g32p_row04_traceSegment_004_0000_0108, g32p_row04_traceSegment_004_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 216 13 14, g32p_row04_traceSegment_004_0216_0013, g32p_row04_traceSegment_004_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 243 13 14, g32p_row04_traceSegment_004_0243_0013, g32p_row04_traceSegment_004_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 216 27 27, g32p_row04_traceSegment_004_0216_0027, g32p_row04_traceSegment_004_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 270 13 14, g32p_row04_traceSegment_004_0270_0013, g32p_row04_traceSegment_004_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 297 13 14, g32p_row04_traceSegment_004_0297_0013, g32p_row04_traceSegment_004_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 270 27 27, g32p_row04_traceSegment_004_0270_0027, g32p_row04_traceSegment_004_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 216 54 54, g32p_row04_traceSegment_004_0216_0054, g32p_row04_traceSegment_004_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 324 13 14, g32p_row04_traceSegment_004_0324_0013, g32p_row04_traceSegment_004_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 351 13 14, g32p_row04_traceSegment_004_0351_0013, g32p_row04_traceSegment_004_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 324 27 27, g32p_row04_traceSegment_004_0324_0027, g32p_row04_traceSegment_004_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 378 13 14, g32p_row04_traceSegment_004_0378_0013, g32p_row04_traceSegment_004_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 405 13 14, g32p_row04_traceSegment_004_0405_0013, g32p_row04_traceSegment_004_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 378 27 27, g32p_row04_traceSegment_004_0378_0027, g32p_row04_traceSegment_004_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 324 54 54, g32p_row04_traceSegment_004_0324_0054, g32p_row04_traceSegment_004_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_004 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 216 108 108, g32p_row04_traceSegment_004_0216_0108, g32p_row04_traceSegment_004_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_004 0 432 = [4, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 0 216 216, g32p_row04_traceSegment_004_0000_0216, g32p_row04_traceSegment_004_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 432 13 14, g32p_row04_traceSegment_004_0432_0013, g32p_row04_traceSegment_004_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 459 13 14, g32p_row04_traceSegment_004_0459_0013, g32p_row04_traceSegment_004_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 432 27 27, g32p_row04_traceSegment_004_0432_0027, g32p_row04_traceSegment_004_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 486 13 14, g32p_row04_traceSegment_004_0486_0013, g32p_row04_traceSegment_004_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 513 13 14, g32p_row04_traceSegment_004_0513_0013, g32p_row04_traceSegment_004_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 486 27 27, g32p_row04_traceSegment_004_0486_0027, g32p_row04_traceSegment_004_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 432 54 54, g32p_row04_traceSegment_004_0432_0054, g32p_row04_traceSegment_004_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 540 13 14, g32p_row04_traceSegment_004_0540_0013, g32p_row04_traceSegment_004_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 580 14 = [4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 567 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 567 13 14, g32p_row04_traceSegment_004_0567_0013, g32p_row04_traceSegment_004_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 540 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 540 27 27, g32p_row04_traceSegment_004_0540_0027, g32p_row04_traceSegment_004_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 594 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 607 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 594 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 594 13 14, g32p_row04_traceSegment_004_0594_0013, g32p_row04_traceSegment_004_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 621 13 14, g32p_row04_traceSegment_004_0621_0013, g32p_row04_traceSegment_004_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 594 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 594 27 27, g32p_row04_traceSegment_004_0594_0027, g32p_row04_traceSegment_004_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 540 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 540 54 54, g32p_row04_traceSegment_004_0540_0054, g32p_row04_traceSegment_004_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_004 432 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 432 108 108, g32p_row04_traceSegment_004_0432_0108, g32p_row04_traceSegment_004_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 648 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 648 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 648 13 14, g32p_row04_traceSegment_004_0648_0013, g32p_row04_traceSegment_004_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 688 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 675 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 675 13 14, g32p_row04_traceSegment_004_0675_0013, g32p_row04_traceSegment_004_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 648 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 648 27 27, g32p_row04_traceSegment_004_0648_0027, g32p_row04_traceSegment_004_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 702 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 702 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 702 13 14, g32p_row04_traceSegment_004_0702_0013, g32p_row04_traceSegment_004_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 729 13 14, g32p_row04_traceSegment_004_0729_0013, g32p_row04_traceSegment_004_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 702 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 702 27 27, g32p_row04_traceSegment_004_0702_0027, g32p_row04_traceSegment_004_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 648 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 648 54 54, g32p_row04_traceSegment_004_0648_0054, g32p_row04_traceSegment_004_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 756 13 14, g32p_row04_traceSegment_004_0756_0013, g32p_row04_traceSegment_004_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 783 13 14, g32p_row04_traceSegment_004_0783_0013, g32p_row04_traceSegment_004_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 756 27 27, g32p_row04_traceSegment_004_0756_0027, g32p_row04_traceSegment_004_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 823 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 810 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 810 13 14, g32p_row04_traceSegment_004_0810_0013, g32p_row04_traceSegment_004_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 837 13 14, g32p_row04_traceSegment_004_0837_0013, g32p_row04_traceSegment_004_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 810 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 810 27 27, g32p_row04_traceSegment_004_0810_0027, g32p_row04_traceSegment_004_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 756 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 756 54 54, g32p_row04_traceSegment_004_0756_0054, g32p_row04_traceSegment_004_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_004 648 216 = [4, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 648 108 108, g32p_row04_traceSegment_004_0648_0108, g32p_row04_traceSegment_004_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_004 432 432 = [10, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 432 216 216, g32p_row04_traceSegment_004_0432_0216, g32p_row04_traceSegment_004_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_004 0 864 = [14, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 0 432 432, g32p_row04_traceSegment_004_0000_0432, g32p_row04_traceSegment_004_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 864 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 877 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 864 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 864 13 14, g32p_row04_traceSegment_004_0864_0013, g32p_row04_traceSegment_004_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 904 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 891 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 891 13 14, g32p_row04_traceSegment_004_0891_0013, g32p_row04_traceSegment_004_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 864 54 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 864 27 27, g32p_row04_traceSegment_004_0864_0027, g32p_row04_traceSegment_004_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 918 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 918 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 918 13 14, g32p_row04_traceSegment_004_0918_0013, g32p_row04_traceSegment_004_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 945 13 14, g32p_row04_traceSegment_004_0945_0013, g32p_row04_traceSegment_004_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 918 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 918 27 27, g32p_row04_traceSegment_004_0918_0027, g32p_row04_traceSegment_004_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 864 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 864 54 54, g32p_row04_traceSegment_004_0864_0054, g32p_row04_traceSegment_004_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 972 13 14, g32p_row04_traceSegment_004_0972_0013, g32p_row04_traceSegment_004_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 999 13 14, g32p_row04_traceSegment_004_0999_0013, g32p_row04_traceSegment_004_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 972 27 27, g32p_row04_traceSegment_004_0972_0027, g32p_row04_traceSegment_004_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1026 13 14, g32p_row04_traceSegment_004_1026_0013, g32p_row04_traceSegment_004_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1053 13 14, g32p_row04_traceSegment_004_1053_0013, g32p_row04_traceSegment_004_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1026 27 27, g32p_row04_traceSegment_004_1026_0027, g32p_row04_traceSegment_004_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 972 54 54, g32p_row04_traceSegment_004_0972_0054, g32p_row04_traceSegment_004_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_004 864 216 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 864 108 108, g32p_row04_traceSegment_004_0864_0108, g32p_row04_traceSegment_004_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1080 13 14, g32p_row04_traceSegment_004_1080_0013, g32p_row04_traceSegment_004_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1107 13 14, g32p_row04_traceSegment_004_1107_0013, g32p_row04_traceSegment_004_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1080 27 27, g32p_row04_traceSegment_004_1080_0027, g32p_row04_traceSegment_004_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1134 13 14, g32p_row04_traceSegment_004_1134_0013, g32p_row04_traceSegment_004_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1174 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1161 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1161 13 14, g32p_row04_traceSegment_004_1161_0013, g32p_row04_traceSegment_004_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1134 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1134 27 27, g32p_row04_traceSegment_004_1134_0027, g32p_row04_traceSegment_004_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 1080 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1080 54 54, g32p_row04_traceSegment_004_1080_0054, g32p_row04_traceSegment_004_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1188 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1188 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1188 13 14, g32p_row04_traceSegment_004_1188_0013, g32p_row04_traceSegment_004_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1215 13 14, g32p_row04_traceSegment_004_1215_0013, g32p_row04_traceSegment_004_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1188 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1188 27 27, g32p_row04_traceSegment_004_1188_0027, g32p_row04_traceSegment_004_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1242 13 14, g32p_row04_traceSegment_004_1242_0013, g32p_row04_traceSegment_004_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1269 13 14, g32p_row04_traceSegment_004_1269_0013, g32p_row04_traceSegment_004_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1242 27 27, g32p_row04_traceSegment_004_1242_0027, g32p_row04_traceSegment_004_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 1188 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1188 54 54, g32p_row04_traceSegment_004_1188_0054, g32p_row04_traceSegment_004_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_004 1080 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1080 108 108, g32p_row04_traceSegment_004_1080_0108, g32p_row04_traceSegment_004_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_004 864 432 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 864 216 216, g32p_row04_traceSegment_004_0864_0216, g32p_row04_traceSegment_004_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1296 13 14, g32p_row04_traceSegment_004_1296_0013, g32p_row04_traceSegment_004_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1323 13 14, g32p_row04_traceSegment_004_1323_0013, g32p_row04_traceSegment_004_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1296 27 27, g32p_row04_traceSegment_004_1296_0027, g32p_row04_traceSegment_004_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1350 13 14, g32p_row04_traceSegment_004_1350_0013, g32p_row04_traceSegment_004_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1377 13 14, g32p_row04_traceSegment_004_1377_0013, g32p_row04_traceSegment_004_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1350 27 27, g32p_row04_traceSegment_004_1350_0027, g32p_row04_traceSegment_004_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1296 54 54, g32p_row04_traceSegment_004_1296_0054, g32p_row04_traceSegment_004_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1404 13 14, g32p_row04_traceSegment_004_1404_0013, g32p_row04_traceSegment_004_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1431 13 14, g32p_row04_traceSegment_004_1431_0013, g32p_row04_traceSegment_004_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1404 27 27, g32p_row04_traceSegment_004_1404_0027, g32p_row04_traceSegment_004_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1458 13 14, g32p_row04_traceSegment_004_1458_0013, g32p_row04_traceSegment_004_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1485 13 14, g32p_row04_traceSegment_004_1485_0013, g32p_row04_traceSegment_004_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1458 27 27, g32p_row04_traceSegment_004_1458_0027, g32p_row04_traceSegment_004_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1404 54 54, g32p_row04_traceSegment_004_1404_0054, g32p_row04_traceSegment_004_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_004 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1296 108 108, g32p_row04_traceSegment_004_1296_0108, g32p_row04_traceSegment_004_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1512 13 14, g32p_row04_traceSegment_004_1512_0013, g32p_row04_traceSegment_004_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1539 13 14, g32p_row04_traceSegment_004_1539_0013, g32p_row04_traceSegment_004_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1512 27 27, g32p_row04_traceSegment_004_1512_0027, g32p_row04_traceSegment_004_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1566 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1566 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1566 13 14, g32p_row04_traceSegment_004_1566_0013, g32p_row04_traceSegment_004_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1593 13 14, g32p_row04_traceSegment_004_1593_0013, g32p_row04_traceSegment_004_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1566 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1566 27 27, g32p_row04_traceSegment_004_1566_0027, g32p_row04_traceSegment_004_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 1512 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1512 54 54, g32p_row04_traceSegment_004_1512_0054, g32p_row04_traceSegment_004_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1620 13 14, g32p_row04_traceSegment_004_1620_0013, g32p_row04_traceSegment_004_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1647 13 14, g32p_row04_traceSegment_004_1647_0013, g32p_row04_traceSegment_004_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1620 27 27, g32p_row04_traceSegment_004_1620_0027, g32p_row04_traceSegment_004_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1674 13 14, g32p_row04_traceSegment_004_1674_0013, g32p_row04_traceSegment_004_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_004 1701 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_004 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_004_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_004 1701 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1701 13 14, g32p_row04_traceSegment_004_1701_0013, g32p_row04_traceSegment_004_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_004 1674 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1674 27 27, g32p_row04_traceSegment_004_1674_0027, g32p_row04_traceSegment_004_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_004 1620 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1620 54 54, g32p_row04_traceSegment_004_1620_0054, g32p_row04_traceSegment_004_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_004 1512 216 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1512 108 108, g32p_row04_traceSegment_004_1512_0108, g32p_row04_traceSegment_004_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_004_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_004 1296 432 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 1296 216 216, g32p_row04_traceSegment_004_1296_0216, g32p_row04_traceSegment_004_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_004 864 864 = [2, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 864 432 432, g32p_row04_traceSegment_004_0864_0432, g32p_row04_traceSegment_004_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_004_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_004 0 1728 = [16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_004 0 864 864, g32p_row04_traceSegment_004_0000_0864, g32p_row04_traceSegment_004_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 4 = [16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_004_0000_1728

end HodgeLean.Foundations.Program

end
end
