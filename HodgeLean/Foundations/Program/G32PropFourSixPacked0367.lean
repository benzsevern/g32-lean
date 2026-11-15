import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow17
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

def g32p_supplierGroup12_source : Fin 1296 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 648 then (if i.val < 324 then (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (92, 216)) else (if i.val < 3 then (79, 11) else (if i.val < 4 then (82, 247) else (26, 93)))) else (if i.val < 7 then (if i.val < 6 then (21, 123) else (50, 18)) else (if i.val < 8 then (92, 201) else (if i.val < 9 then (132, 243) else (51, 45))))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then (0, 96) else (49, 68)) else (if i.val < 13 then (10, 83) else (if i.val < 14 then (113, 10) else (49, 185)))) else (if i.val < 17 then (if i.val < 16 then (68, 170) else (45, 234)) else (if i.val < 18 then (133, 21) else (if i.val < 19 then (65, 50) else (115, 3)))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then (120, 101) else (9, 135)) else (if i.val < 23 then (117, 23) else (if i.val < 24 then (83, 215) else (12, 196)))) else (if i.val < 27 then (if i.val < 26 then (72, 96) else (38, 174)) else (if i.val < 28 then (20, 254) else (if i.val < 29 then (95, 201) else (15, 167))))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then (109, 126) else (137, 70)) else (if i.val < 33 then (44, 236) else (if i.val < 34 then (144, 205) else (133, 122)))) else (if i.val < 37 then (if i.val < 36 then (9, 18) else (137, 73)) else (if i.val < 38 then (2, 82) else (if i.val < 39 then (131, 162) else (9, 243))))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then (72, 114) else (37, 177)) else (if i.val < 43 then (142, 125) else (if i.val < 44 then (79, 150) else (130, 56)))) else (if i.val < 47 then (if i.val < 46 then (141, 37) else (26, 42)) else (if i.val < 48 then (42, 249) else (if i.val < 49 then (126, 154) else (132, 35))))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then (113, 137) else (77, 194)) else (if i.val < 53 then (105, 159) else (if i.val < 54 then (52, 246) else (129, 219)))) else (if i.val < 57 then (if i.val < 56 then (78, 220) else (0, 99)) else (if i.val < 58 then (5, 194) else (if i.val < 59 then (141, 180) else (107, 240)))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then (27, 15) else (45, 220)) else (if i.val < 63 then (68, 18) else (if i.val < 64 then (132, 234) else (139, 192)))) else (if i.val < 67 then (if i.val < 66 then (82, 230) else (4, 136)) else (if i.val < 68 then (51, 143) else (if i.val < 69 then (25, 188) else (108, 136))))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then (11, 154) else (61, 0)) else (if i.val < 73 then (73, 254) else (if i.val < 74 then (85, 180) else (86, 45)))) else (if i.val < 78 then (if i.val < 76 then (144, 120) else (if i.val < 77 then (111, 220) else (135, 252))) else (if i.val < 79 then (73, 170) else (if i.val < 80 then (138, 64) else (31, 188)))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then (35, 152) else (19, 196)) else (if i.val < 84 then (0, 97) else (if i.val < 85 then (49, 210) else (10, 188)))) else (if i.val < 88 then (if i.val < 87 then (53, 162) else (35, 71)) else (if i.val < 89 then (105, 184) else (if i.val < 90 then (62, 23) else (142, 192))))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then (66, 54) else (136, 28)) else (if i.val < 94 then (17, 77) else (if i.val < 95 then (134, 169) else (13, 86)))) else (if i.val < 98 then (if i.val < 97 then (40, 253) else (121, 184)) else (if i.val < 99 then (50, 44) else (if i.val < 100 then (120, 171) else (120, 150)))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then (20, 200) else (120, 146)) else (if i.val < 104 then (101, 30) else (if i.val < 105 then (124, 10) else (135, 195)))) else (if i.val < 108 then (if i.val < 107 then (90, 174) else (142, 78)) else (if i.val < 109 then (81, 24) else (if i.val < 110 then (70, 36) else (3, 231))))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then (136, 15) else (11, 75)) else (if i.val < 114 then (38, 3) else (if i.val < 115 then (99, 101) else (70, 15)))) else (if i.val < 118 then (if i.val < 117 then (85, 15) else (111, 235)) else (if i.val < 119 then (82, 196) else (if i.val < 120 then (133, 22) else (116, 105))))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then (80, 139) else (113, 190)) else (if i.val < 124 then (28, 77) else (if i.val < 125 then (10, 54) else (53, 17)))) else (if i.val < 128 then (if i.val < 127 then (77, 1) else (45, 151)) else (if i.val < 129 then (0, 101) else (if i.val < 130 then (144, 160) else (99, 131))))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then (88, 204) else (106, 138)) else (if i.val < 134 then (107, 212) else (if i.val < 135 then (57, 37) else (44, 253)))) else (if i.val < 138 then (if i.val < 137 then (142, 202) else (130, 4)) else (if i.val < 139 then (79, 12) else (if i.val < 140 then (98, 20) else (93, 169)))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then (43, 61) else (61, 23)) else (if i.val < 144 then (59, 133) else (if i.val < 145 then (86, 50) else (142, 150)))) else (if i.val < 148 then (if i.val < 147 then (135, 166) else (73, 157)) else (if i.val < 149 then (132, 99) else (if i.val < 150 then (80, 186) else (141, 8))))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then (57, 11) else (67, 84)) else (if i.val < 154 then (97, 197) else (if i.val < 155 then (104, 231) else (133, 35)))) else (if i.val < 159 then (if i.val < 157 then (23, 69) else (if i.val < 158 then (129, 245) else (115, 49))) else (if i.val < 160 then (132, 33) else (if i.val < 161 then (138, 38) else (97, 251))))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then (142, 248) else (144, 96)) else (if i.val < 165 then (85, 37) else (if i.val < 166 then (141, 143) else (30, 7)))) else (if i.val < 169 then (if i.val < 168 then (127, 21) else (9, 25)) else (if i.val < 170 then (93, 157) else (if i.val < 171 then (141, 253) else (34, 153))))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then (21, 87) else (77, 79)) else (if i.val < 175 then (142, 9) else (if i.val < 176 then (100, 132) else (79, 93)))) else (if i.val < 179 then (if i.val < 178 then (79, 202) else (43, 124)) else (if i.val < 180 then (41, 221) else (if i.val < 181 then (99, 20) else (137, 138)))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then (106, 134) else (29, 134)) else (if i.val < 185 then (38, 100) else (if i.val < 186 then (128, 141) else (33, 148)))) else (if i.val < 189 then (if i.val < 188 then (90, 168) else (111, 60)) else (if i.val < 190 then (138, 96) else (if i.val < 191 then (89, 82) else (9, 227))))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then (39, 96) else (121, 240)) else (if i.val < 195 then (70, 176) else (if i.val < 196 then (65, 74) else (132, 94)))) else (if i.val < 199 then (if i.val < 198 then (142, 203) else (18, 199)) else (if i.val < 200 then (17, 95) else (if i.val < 201 then (130, 12) else (61, 193))))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then (96, 13) else (72, 226)) else (if i.val < 205 then (7, 127) else (if i.val < 206 then (9, 125) else (77, 116)))) else (if i.val < 209 then (if i.val < 208 then (74, 233) else (139, 211)) else (if i.val < 210 then (135, 81) else (if i.val < 211 then (121, 31) else (13, 96))))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then (33, 80) else (142, 115)) else (if i.val < 215 then (134, 153) else (if i.val < 216 then (98, 8) else (135, 196)))) else (if i.val < 219 then (if i.val < 218 then (87, 242) else (77, 188)) else (if i.val < 220 then (129, 99) else (if i.val < 221 then (10, 213) else (138, 70)))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then (27, 168) else (52, 37)) else (if i.val < 225 then (21, 75) else (if i.val < 226 then (33, 68) else (34, 170)))) else (if i.val < 229 then (if i.val < 228 then (39, 229) else (50, 122)) else (if i.val < 230 then (132, 30) else (if i.val < 231 then (132, 182) else (127, 83))))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then (94, 107) else (120, 179)) else (if i.val < 235 then (89, 224) else (if i.val < 236 then (42, 179) else (72, 236)))) else (if i.val < 240 then (if i.val < 238 then (97, 30) else (if i.val < 239 then (80, 239) else (89, 15))) else (if i.val < 241 then (44, 86) else (if i.val < 242 then (143, 124) else (63, 17)))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then (143, 6) else (1, 98)) else (if i.val < 246 then (111, 65) else (if i.val < 247 then (143, 132) else (54, 142)))) else (if i.val < 250 then (if i.val < 249 then (67, 222) else (83, 161)) else (if i.val < 251 then (103, 124) else (if i.val < 252 then (133, 228) else (12, 131))))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then (18, 120) else (39, 64)) else (if i.val < 256 then (141, 212) else (if i.val < 257 then (49, 167) else (26, 78)))) else (if i.val < 260 then (if i.val < 259 then (127, 133) else (101, 223)) else (if i.val < 261 then (3, 9) else (if i.val < 262 then (1, 33) else (76, 212)))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then (144, 141) else (27, 196)) else (if i.val < 266 then (100, 251) else (if i.val < 267 then (4, 245) else (108, 226)))) else (if i.val < 270 then (if i.val < 269 then (79, 20) else (137, 172)) else (if i.val < 271 then (134, 143) else (if i.val < 272 then (133, 150) else (137, 95))))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then (144, 134) else (2, 64)) else (if i.val < 276 then (53, 180) else (if i.val < 277 then (111, 87) else (121, 1)))) else (if i.val < 280 then (if i.val < 279 then (112, 115) else (33, 136)) else (if i.val < 281 then (89, 115) else (if i.val < 282 then (136, 59) else (98, 71))))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then (6, 86) else (126, 224)) else (if i.val < 286 then (111, 241) else (if i.val < 287 then (135, 158) else (76, 108)))) else (if i.val < 290 then (if i.val < 289 then (135, 77) else (33, 181)) else (if i.val < 291 then (132, 207) else (if i.val < 292 then (67, 149) else (125, 43))))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then (79, 155) else (133, 194)) else (if i.val < 296 then (66, 68) else (if i.val < 297 then (4, 22) else (55, 151)))) else (if i.val < 300 then (if i.val < 299 then (118, 208) else (119, 205)) else (if i.val < 301 then (124, 14) else (if i.val < 302 then (60, 240) else (112, 161)))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then (66, 174) else (137, 193)) else (if i.val < 306 then (100, 42) else (if i.val < 307 then (133, 54) else (86, 86)))) else (if i.val < 310 then (if i.val < 309 then (51, 234) else (5, 115)) else (if i.val < 311 then (7, 123) else (if i.val < 312 then (127, 78) else (73, 150))))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then (122, 119) else (133, 159)) else (if i.val < 316 then (92, 211) else (if i.val < 317 then (82, 134) else (131, 84)))) else (if i.val < 321 then (if i.val < 319 then (39, 243) else (if i.val < 320 then (123, 137) else (90, 247))) else (if i.val < 322 then (126, 61) else (if i.val < 323 then (85, 139) else (42, 142)))))))))) else (if i.val < 486 then (if i.val < 405 then (if i.val < 364 then (if i.val < 344 then (if i.val < 334 then (if i.val < 329 then (if i.val < 326 then (if i.val < 325 then (32, 39) else (108, 15)) else (if i.val < 327 then (97, 165) else (if i.val < 328 then (99, 144) else (140, 82)))) else (if i.val < 331 then (if i.val < 330 then (25, 126) else (91, 198)) else (if i.val < 332 then (66, 164) else (if i.val < 333 then (123, 184) else (125, 130))))) else (if i.val < 339 then (if i.val < 336 then (if i.val < 335 then (10, 0) else (122, 66)) else (if i.val < 337 then (76, 43) else (if i.val < 338 then (76, 181) else (74, 126)))) else (if i.val < 341 then (if i.val < 340 then (19, 19) else (5, 121)) else (if i.val < 342 then (63, 225) else (if i.val < 343 then (31, 88) else (22, 50)))))) else (if i.val < 354 then (if i.val < 349 then (if i.val < 346 then (if i.val < 345 then (143, 225) else (71, 53)) else (if i.val < 347 then (45, 3) else (if i.val < 348 then (37, 167) else (81, 11)))) else (if i.val < 351 then (if i.val < 350 then (142, 200) else (74, 203)) else (if i.val < 352 then (50, 108) else (if i.val < 353 then (118, 108) else (113, 134))))) else (if i.val < 359 then (if i.val < 356 then (if i.val < 355 then (142, 110) else (144, 184)) else (if i.val < 357 then (117, 72) else (if i.val < 358 then (86, 136) else (133, 177)))) else (if i.val < 361 then (if i.val < 360 then (123, 205) else (79, 84)) else (if i.val < 362 then (67, 201) else (if i.val < 363 then (131, 170) else (101, 184))))))) else (if i.val < 384 then (if i.val < 374 then (if i.val < 369 then (if i.val < 366 then (if i.val < 365 then (44, 183) else (118, 3)) else (if i.val < 367 then (133, 19) else (if i.val < 368 then (140, 3) else (133, 14)))) else (if i.val < 371 then (if i.val < 370 then (14, 242) else (133, 144)) else (if i.val < 372 then (16, 11) else (if i.val < 373 then (143, 146) else (139, 78))))) else (if i.val < 379 then (if i.val < 376 then (if i.val < 375 then (128, 194) else (79, 107)) else (if i.val < 377 then (99, 25) else (if i.val < 378 then (106, 70) else (95, 241)))) else (if i.val < 381 then (if i.val < 380 then (110, 81) else (126, 213)) else (if i.val < 382 then (79, 68) else (if i.val < 383 then (144, 55) else (142, 21)))))) else (if i.val < 394 then (if i.val < 389 then (if i.val < 386 then (if i.val < 385 then (29, 39) else (126, 114)) else (if i.val < 387 then (17, 96) else (if i.val < 388 then (102, 14) else (89, 219)))) else (if i.val < 391 then (if i.val < 390 then (92, 241) else (87, 29)) else (if i.val < 392 then (79, 158) else (if i.val < 393 then (65, 114) else (17, 232))))) else (if i.val < 399 then (if i.val < 396 then (if i.val < 395 then (88, 247) else (143, 221)) else (if i.val < 397 then (104, 124) else (if i.val < 398 then (14, 86) else (124, 66)))) else (if i.val < 402 then (if i.val < 400 then (129, 90) else (if i.val < 401 then (11, 7) else (26, 20))) else (if i.val < 403 then (126, 100) else (if i.val < 404 then (120, 190) else (5, 188)))))))) else (if i.val < 445 then (if i.val < 425 then (if i.val < 415 then (if i.val < 410 then (if i.val < 407 then (if i.val < 406 then (131, 152) else (140, 254)) else (if i.val < 408 then (58, 209) else (if i.val < 409 then (54, 253) else (108, 236)))) else (if i.val < 412 then (if i.val < 411 then (131, 182) else (113, 148)) else (if i.val < 413 then (138, 23) else (if i.val < 414 then (90, 177) else (144, 152))))) else (if i.val < 420 then (if i.val < 417 then (if i.val < 416 then (123, 103) else (88, 196)) else (if i.val < 418 then (49, 64) else (if i.val < 419 then (143, 29) else (106, 45)))) else (if i.val < 422 then (if i.val < 421 then (42, 187) else (122, 16)) else (if i.val < 423 then (34, 45) else (if i.val < 424 then (118, 173) else (127, 111)))))) else (if i.val < 435 then (if i.val < 430 then (if i.val < 427 then (if i.val < 426 then (62, 249) else (68, 239)) else (if i.val < 428 then (127, 49) else (if i.val < 429 then (103, 219) else (5, 93)))) else (if i.val < 432 then (if i.val < 431 then (121, 123) else (136, 33)) else (if i.val < 433 then (128, 15) else (if i.val < 434 then (96, 204) else (124, 207))))) else (if i.val < 440 then (if i.val < 437 then (if i.val < 436 then (39, 126) else (66, 158)) else (if i.val < 438 then (27, 36) else (if i.val < 439 then (129, 226) else (136, 139)))) else (if i.val < 442 then (if i.val < 441 then (17, 146) else (23, 30)) else (if i.val < 443 then (133, 79) else (if i.val < 444 then (111, 102) else (80, 232))))))) else (if i.val < 465 then (if i.val < 455 then (if i.val < 450 then (if i.val < 447 then (if i.val < 446 then (47, 13) else (50, 197)) else (if i.val < 448 then (117, 148) else (if i.val < 449 then (114, 33) else (76, 250)))) else (if i.val < 452 then (if i.val < 451 then (60, 48) else (61, 21)) else (if i.val < 453 then (82, 85) else (if i.val < 454 then (144, 192) else (32, 229))))) else (if i.val < 460 then (if i.val < 457 then (if i.val < 456 then (19, 140) else (46, 91)) else (if i.val < 458 then (76, 210) else (if i.val < 459 then (114, 113) else (134, 241)))) else (if i.val < 462 then (if i.val < 461 then (131, 97) else (67, 137)) else (if i.val < 463 then (24, 118) else (if i.val < 464 then (138, 215) else (99, 183)))))) else (if i.val < 475 then (if i.val < 470 then (if i.val < 467 then (if i.val < 466 then (113, 252) else (119, 181)) else (if i.val < 468 then (83, 28) else (if i.val < 469 then (100, 243) else (19, 222)))) else (if i.val < 472 then (if i.val < 471 then (38, 233) else (119, 242)) else (if i.val < 473 then (69, 3) else (if i.val < 474 then (144, 49) else (72, 168))))) else (if i.val < 480 then (if i.val < 477 then (if i.val < 476 then (143, 228) else (11, 21)) else (if i.val < 478 then (36, 168) else (if i.val < 479 then (37, 41) else (133, 4)))) else (if i.val < 483 then (if i.val < 481 then (120, 167) else (if i.val < 482 then (133, 151) else (5, 47))) else (if i.val < 484 then (118, 138) else (if i.val < 485 then (72, 255) else (92, 134))))))))) else (if i.val < 567 then (if i.val < 526 then (if i.val < 506 then (if i.val < 496 then (if i.val < 491 then (if i.val < 488 then (if i.val < 487 then (130, 220) else (92, 20)) else (if i.val < 489 then (144, 70) else (if i.val < 490 then (134, 72) else (42, 58)))) else (if i.val < 493 then (if i.val < 492 then (137, 176) else (11, 253)) else (if i.val < 494 then (94, 38) else (if i.val < 495 then (79, 192) else (99, 113))))) else (if i.val < 501 then (if i.val < 498 then (if i.val < 497 then (70, 192) else (76, 46)) else (if i.val < 499 then (78, 89) else (if i.val < 500 then (121, 49) else (119, 121)))) else (if i.val < 503 then (if i.val < 502 then (70, 234) else (116, 113)) else (if i.val < 504 then (142, 77) else (if i.val < 505 then (139, 175) else (113, 0)))))) else (if i.val < 516 then (if i.val < 511 then (if i.val < 508 then (if i.val < 507 then (41, 84) else (66, 132)) else (if i.val < 509 then (141, 129) else (if i.val < 510 then (1, 101) else (49, 99)))) else (if i.val < 513 then (if i.val < 512 then (25, 71) else (125, 118)) else (if i.val < 514 then (29, 48) else (if i.val < 515 then (123, 240) else (121, 161))))) else (if i.val < 521 then (if i.val < 518 then (if i.val < 517 then (128, 199) else (90, 209)) else (if i.val < 519 then (78, 107) else (if i.val < 520 then (111, 16) else (86, 73)))) else (if i.val < 523 then (if i.val < 522 then (127, 112) else (81, 214)) else (if i.val < 524 then (121, 146) else (if i.val < 525 then (116, 85) else (82, 169))))))) else (if i.val < 546 then (if i.val < 536 then (if i.val < 531 then (if i.val < 528 then (if i.val < 527 then (9, 203) else (134, 1)) else (if i.val < 529 then (144, 175) else (if i.val < 530 then (36, 187) else (33, 62)))) else (if i.val < 533 then (if i.val < 532 then (34, 117) else (132, 67)) else (if i.val < 534 then (48, 191) else (if i.val < 535 then (84, 207) else (131, 96))))) else (if i.val < 541 then (if i.val < 538 then (if i.val < 537 then (32, 104) else (23, 22)) else (if i.val < 539 then (25, 99) else (if i.val < 540 then (122, 247) else (36, 125)))) else (if i.val < 543 then (if i.val < 542 then (103, 157) else (43, 168)) else (if i.val < 544 then (28, 69) else (if i.val < 545 then (119, 44) else (68, 100)))))) else (if i.val < 556 then (if i.val < 551 then (if i.val < 548 then (if i.val < 547 then (130, 208) else (84, 190)) else (if i.val < 549 then (38, 42) else (if i.val < 550 then (117, 60) else (36, 158)))) else (if i.val < 553 then (if i.val < 552 then (54, 39) else (31, 205)) else (if i.val < 554 then (139, 186) else (if i.val < 555 then (135, 32) else (128, 226))))) else (if i.val < 561 then (if i.val < 558 then (if i.val < 557 then (85, 250) else (135, 68)) else (if i.val < 559 then (142, 44) else (if i.val < 560 then (124, 180) else (50, 240)))) else (if i.val < 564 then (if i.val < 562 then (81, 27) else (if i.val < 563 then (42, 13) else (60, 112))) else (if i.val < 565 then (78, 186) else (if i.val < 566 then (144, 157) else (89, 35)))))))) else (if i.val < 607 then (if i.val < 587 then (if i.val < 577 then (if i.val < 572 then (if i.val < 569 then (if i.val < 568 then (64, 167) else (67, 77)) else (if i.val < 570 then (144, 83) else (if i.val < 571 then (26, 118) else (142, 51)))) else (if i.val < 574 then (if i.val < 573 then (121, 177) else (49, 187)) else (if i.val < 575 then (131, 59) else (if i.val < 576 then (107, 35) else (9, 211))))) else (if i.val < 582 then (if i.val < 579 then (if i.val < 578 then (32, 135) else (118, 104)) else (if i.val < 580 then (88, 166) else (if i.val < 581 then (142, 208) else (25, 13)))) else (if i.val < 584 then (if i.val < 583 then (70, 212) else (142, 254)) else (if i.val < 585 then (103, 223) else (if i.val < 586 then (10, 9) else (1, 190)))))) else (if i.val < 597 then (if i.val < 592 then (if i.val < 589 then (if i.val < 588 then (57, 34) else (22, 210)) else (if i.val < 590 then (81, 193) else (if i.val < 591 then (141, 140) else (56, 152)))) else (if i.val < 594 then (if i.val < 593 then (85, 96) else (111, 135)) else (if i.val < 595 then (94, 22) else (if i.val < 596 then (82, 34) else (63, 250))))) else (if i.val < 602 then (if i.val < 599 then (if i.val < 598 then (23, 103) else (84, 45)) else (if i.val < 600 then (34, 97) else (if i.val < 601 then (105, 203) else (143, 28)))) else (if i.val < 604 then (if i.val < 603 then (22, 101) else (58, 163)) else (if i.val < 605 then (127, 114) else (if i.val < 606 then (101, 4) else (14, 235))))))) else (if i.val < 627 then (if i.val < 617 then (if i.val < 612 then (if i.val < 609 then (if i.val < 608 then (0, 37) else (95, 17)) else (if i.val < 610 then (141, 159) else (if i.val < 611 then (31, 113) else (144, 13)))) else (if i.val < 614 then (if i.val < 613 then (61, 108) else (40, 102)) else (if i.val < 615 then (43, 145) else (if i.val < 616 then (47, 7) else (116, 178))))) else (if i.val < 622 then (if i.val < 619 then (if i.val < 618 then (138, 82) else (11, 6)) else (if i.val < 620 then (113, 163) else (if i.val < 621 then (77, 163) else (102, 165)))) else (if i.val < 624 then (if i.val < 623 then (48, 50) else (143, 199)) else (if i.val < 625 then (55, 213) else (if i.val < 626 then (80, 5) else (118, 160)))))) else (if i.val < 637 then (if i.val < 632 then (if i.val < 629 then (if i.val < 628 then (131, 129) else (132, 226)) else (if i.val < 630 then (141, 210) else (if i.val < 631 then (15, 23) else (5, 18)))) else (if i.val < 634 then (if i.val < 633 then (84, 33) else (53, 228)) else (if i.val < 635 then (42, 210) else (if i.val < 636 then (80, 43) else (4, 196))))) else (if i.val < 642 then (if i.val < 639 then (if i.val < 638 then (139, 203) else (34, 8)) else (if i.val < 640 then (138, 59) else (if i.val < 641 then (110, 198) else (57, 112)))) else (if i.val < 645 then (if i.val < 643 then (71, 4) else (if i.val < 644 then (79, 180) else (77, 43))) else (if i.val < 646 then (119, 209) else (if i.val < 647 then (25, 158) else (28, 241))))))))))) else (if i.val < 972 then (if i.val < 810 then (if i.val < 729 then (if i.val < 688 then (if i.val < 668 then (if i.val < 658 then (if i.val < 653 then (if i.val < 650 then (if i.val < 649 then (143, 206) else (3, 217)) else (if i.val < 651 then (40, 146) else (if i.val < 652 then (43, 182) else (28, 29)))) else (if i.val < 655 then (if i.val < 654 then (141, 222) else (126, 1)) else (if i.val < 656 then (117, 227) else (if i.val < 657 then (1, 207) else (4, 154))))) else (if i.val < 663 then (if i.val < 660 then (if i.val < 659 then (44, 237) else (114, 241)) else (if i.val < 661 then (96, 98) else (if i.val < 662 then (126, 231) else (129, 165)))) else (if i.val < 665 then (if i.val < 664 then (47, 208) else (141, 206)) else (if i.val < 666 then (121, 234) else (if i.val < 667 then (52, 210) else (143, 36)))))) else (if i.val < 678 then (if i.val < 673 then (if i.val < 670 then (if i.val < 669 then (74, 184) else (126, 82)) else (if i.val < 671 then (2, 130) else (if i.val < 672 then (40, 222) else (51, 98)))) else (if i.val < 675 then (if i.val < 674 then (134, 202) else (58, 124)) else (if i.val < 676 then (143, 152) else (if i.val < 677 then (39, 14) else (38, 162))))) else (if i.val < 683 then (if i.val < 680 then (if i.val < 679 then (137, 171) else (71, 122)) else (if i.val < 681 then (141, 181) else (if i.val < 682 then (60, 249) else (60, 252)))) else (if i.val < 685 then (if i.val < 684 then (14, 247) else (78, 73)) else (if i.val < 686 then (92, 208) else (if i.val < 687 then (122, 24) else (17, 157))))))) else (if i.val < 708 then (if i.val < 698 then (if i.val < 693 then (if i.val < 690 then (if i.val < 689 then (119, 142) else (36, 63)) else (if i.val < 691 then (117, 213) else (if i.val < 692 then (79, 255) else (106, 106)))) else (if i.val < 695 then (if i.val < 694 then (43, 64) else (71, 175)) else (if i.val < 696 then (81, 224) else (if i.val < 697 then (127, 22) else (118, 10))))) else (if i.val < 703 then (if i.val < 700 then (if i.val < 699 then (15, 78) else (92, 37)) else (if i.val < 701 then (86, 11) else (if i.val < 702 then (131, 99) else (118, 71)))) else (if i.val < 705 then (if i.val < 704 then (71, 204) else (29, 120)) else (if i.val < 706 then (51, 199) else (if i.val < 707 then (69, 124) else (142, 103)))))) else (if i.val < 718 then (if i.val < 713 then (if i.val < 710 then (if i.val < 709 then (14, 104) else (60, 47)) else (if i.val < 711 then (6, 155) else (if i.val < 712 then (7, 177) else (118, 121)))) else (if i.val < 715 then (if i.val < 714 then (139, 215) else (121, 81)) else (if i.val < 716 then (31, 130) else (if i.val < 717 then (138, 168) else (100, 175))))) else (if i.val < 723 then (if i.val < 720 then (if i.val < 719 then (129, 201) else (111, 10)) else (if i.val < 721 then (119, 22) else (if i.val < 722 then (51, 229) else (100, 79)))) else (if i.val < 726 then (if i.val < 724 then (78, 28) else (if i.val < 725 then (134, 104) else (116, 181))) else (if i.val < 727 then (92, 174) else (if i.val < 728 then (71, 72) else (112, 156)))))))) else (if i.val < 769 then (if i.val < 749 then (if i.val < 739 then (if i.val < 734 then (if i.val < 731 then (if i.val < 730 then (70, 4) else (126, 192)) else (if i.val < 732 then (76, 64) else (if i.val < 733 then (143, 111) else (59, 165)))) else (if i.val < 736 then (if i.val < 735 then (122, 56) else (96, 33)) else (if i.val < 737 then (28, 10) else (if i.val < 738 then (71, 231) else (126, 54))))) else (if i.val < 744 then (if i.val < 741 then (if i.val < 740 then (124, 227) else (55, 24)) else (if i.val < 742 then (92, 168) else (if i.val < 743 then (31, 201) else (31, 106)))) else (if i.val < 746 then (if i.val < 745 then (33, 193) else (67, 63)) else (if i.val < 747 then (136, 10) else (if i.val < 748 then (31, 225) else (59, 68)))))) else (if i.val < 759 then (if i.val < 754 then (if i.val < 751 then (if i.val < 750 then (59, 179) else (104, 187)) else (if i.val < 752 then (108, 108) else (if i.val < 753 then (60, 39) else (121, 15)))) else (if i.val < 756 then (if i.val < 755 then (54, 151) else (77, 61)) else (if i.val < 757 then (84, 224) else (if i.val < 758 then (51, 215) else (59, 170))))) else (if i.val < 764 then (if i.val < 761 then (if i.val < 760 then (48, 157) else (90, 224)) else (if i.val < 762 then (35, 236) else (if i.val < 763 then (92, 45) else (20, 14)))) else (if i.val < 766 then (if i.val < 765 then (67, 91) else (143, 247)) else (if i.val < 767 then (16, 64) else (if i.val < 768 then (106, 233) else (46, 127))))))) else (if i.val < 789 then (if i.val < 779 then (if i.val < 774 then (if i.val < 771 then (if i.val < 770 then (62, 51) else (143, 234)) else (if i.val < 772 then (55, 216) else (if i.val < 773 then (115, 156) else (7, 198)))) else (if i.val < 776 then (if i.val < 775 then (27, 255) else (68, 206)) else (if i.val < 777 then (17, 24) else (if i.val < 778 then (126, 157) else (63, 160))))) else (if i.val < 784 then (if i.val < 781 then (if i.val < 780 then (95, 142) else (138, 224)) else (if i.val < 782 then (41, 49) else (if i.val < 783 then (102, 148) else (59, 87)))) else (if i.val < 786 then (if i.val < 785 then (138, 162) else (133, 208)) else (if i.val < 787 then (103, 83) else (if i.val < 788 then (72, 103) else (41, 239)))))) else (if i.val < 799 then (if i.val < 794 then (if i.val < 791 then (if i.val < 790 then (23, 62) else (88, 148)) else (if i.val < 792 then (104, 241) else (if i.val < 793 then (81, 78) else (32, 231)))) else (if i.val < 796 then (if i.val < 795 then (131, 41) else (73, 108)) else (if i.val < 797 then (70, 27) else (if i.val < 798 then (129, 162) else (52, 27))))) else (if i.val < 804 then (if i.val < 801 then (if i.val < 800 then (109, 241) else (78, 185)) else (if i.val < 802 then (67, 85) else (if i.val < 803 then (46, 43) else (44, 128)))) else (if i.val < 807 then (if i.val < 805 then (85, 18) else (if i.val < 806 then (109, 174) else (143, 99))) else (if i.val < 808 then (103, 255) else (if i.val < 809 then (58, 254) else (17, 99))))))))) else (if i.val < 891 then (if i.val < 850 then (if i.val < 830 then (if i.val < 820 then (if i.val < 815 then (if i.val < 812 then (if i.val < 811 then (137, 84) else (127, 41)) else (if i.val < 813 then (14, 184) else (if i.val < 814 then (130, 242) else (144, 99)))) else (if i.val < 817 then (if i.val < 816 then (100, 246) else (120, 238)) else (if i.val < 818 then (54, 254) else (if i.val < 819 then (50, 161) else (89, 167))))) else (if i.val < 825 then (if i.val < 822 then (if i.val < 821 then (54, 13) else (5, 169)) else (if i.val < 823 then (64, 199) else (if i.val < 824 then (90, 85) else (67, 244)))) else (if i.val < 827 then (if i.val < 826 then (17, 236) else (75, 251)) else (if i.val < 828 then (25, 97) else (if i.val < 829 then (132, 218) else (144, 224)))))) else (if i.val < 840 then (if i.val < 835 then (if i.val < 832 then (if i.val < 831 then (76, 215) else (129, 95)) else (if i.val < 833 then (131, 77) else (if i.val < 834 then (127, 27) else (37, 124)))) else (if i.val < 837 then (if i.val < 836 then (25, 125) else (95, 56)) else (if i.val < 838 then (139, 249) else (if i.val < 839 then (95, 251) else (138, 21))))) else (if i.val < 845 then (if i.val < 842 then (if i.val < 841 then (74, 225) else (6, 177)) else (if i.val < 843 then (85, 110) else (if i.val < 844 then (92, 38) else (58, 148)))) else (if i.val < 847 then (if i.val < 846 then (45, 143) else (60, 11)) else (if i.val < 848 then (70, 42) else (if i.val < 849 then (103, 26) else (136, 75))))))) else (if i.val < 870 then (if i.val < 860 then (if i.val < 855 then (if i.val < 852 then (if i.val < 851 then (83, 97) else (71, 144)) else (if i.val < 853 then (129, 23) else (if i.val < 854 then (18, 219) else (121, 22)))) else (if i.val < 857 then (if i.val < 856 then (95, 154) else (30, 254)) else (if i.val < 858 then (137, 55) else (if i.val < 859 then (90, 181) else (27, 46))))) else (if i.val < 865 then (if i.val < 862 then (if i.val < 861 then (41, 87) else (133, 136)) else (if i.val < 863 then (131, 63) else (if i.val < 864 then (131, 134) else (116, 21)))) else (if i.val < 867 then (if i.val < 866 then (43, 83) else (90, 44)) else (if i.val < 868 then (110, 186) else (if i.val < 869 then (1, 196) else (129, 52)))))) else (if i.val < 880 then (if i.val < 875 then (if i.val < 872 then (if i.val < 871 then (140, 156) else (127, 174)) else (if i.val < 873 then (144, 129) else (if i.val < 874 then (55, 220) else (88, 99)))) else (if i.val < 877 then (if i.val < 876 then (142, 2) else (67, 8)) else (if i.val < 878 then (74, 172) else (if i.val < 879 then (142, 8) else (87, 127))))) else (if i.val < 885 then (if i.val < 882 then (if i.val < 881 then (38, 186) else (142, 48)) else (if i.val < 883 then (118, 201) else (if i.val < 884 then (84, 42) else (89, 66)))) else (if i.val < 888 then (if i.val < 886 then (133, 138) else (if i.val < 887 then (34, 236) else (88, 124))) else (if i.val < 889 then (134, 234) else (if i.val < 890 then (139, 204) else (143, 229)))))))) else (if i.val < 931 then (if i.val < 911 then (if i.val < 901 then (if i.val < 896 then (if i.val < 893 then (if i.val < 892 then (77, 182) else (88, 248)) else (if i.val < 894 then (120, 235) else (if i.val < 895 then (64, 47) else (137, 250)))) else (if i.val < 898 then (if i.val < 897 then (48, 208) else (106, 153)) else (if i.val < 899 then (67, 112) else (if i.val < 900 then (134, 165) else (8, 75))))) else (if i.val < 906 then (if i.val < 903 then (if i.val < 902 then (139, 223) else (127, 29)) else (if i.val < 904 then (0, 34) else (if i.val < 905 then (134, 250) else (135, 173)))) else (if i.val < 908 then (if i.val < 907 then (24, 33) else (88, 82)) else (if i.val < 909 then (127, 223) else (if i.val < 910 then (96, 36) else (80, 76)))))) else (if i.val < 921 then (if i.val < 916 then (if i.val < 913 then (if i.val < 912 then (105, 86) else (118, 91)) else (if i.val < 914 then (62, 58) else (if i.val < 915 then (35, 107) else (92, 61)))) else (if i.val < 918 then (if i.val < 917 then (16, 175) else (79, 90)) else (if i.val < 919 then (143, 67) else (if i.val < 920 then (35, 180) else (96, 14))))) else (if i.val < 926 then (if i.val < 923 then (if i.val < 922 then (125, 245) else (11, 29)) else (if i.val < 924 then (136, 115) else (if i.val < 925 then (130, 217) else (127, 208)))) else (if i.val < 928 then (if i.val < 927 then (128, 235) else (20, 152)) else (if i.val < 929 then (18, 63) else (if i.val < 930 then (127, 69) else (139, 62))))))) else (if i.val < 951 then (if i.val < 941 then (if i.val < 936 then (if i.val < 933 then (if i.val < 932 then (45, 176) else (43, 22)) else (if i.val < 934 then (138, 43) else (if i.val < 935 then (100, 169) else (125, 49)))) else (if i.val < 938 then (if i.val < 937 then (120, 125) else (142, 117)) else (if i.val < 939 then (26, 238) else (if i.val < 940 then (43, 149) else (29, 204))))) else (if i.val < 946 then (if i.val < 943 then (if i.val < 942 then (55, 108) else (19, 178)) else (if i.val < 944 then (105, 180) else (if i.val < 945 then (140, 57) else (111, 90)))) else (if i.val < 948 then (if i.val < 947 then (120, 217) else (83, 54)) else (if i.val < 949 then (134, 40) else (if i.val < 950 then (142, 73) else (8, 99)))))) else (if i.val < 961 then (if i.val < 956 then (if i.val < 953 then (if i.val < 952 then (117, 158) else (131, 126)) else (if i.val < 954 then (140, 214) else (if i.val < 955 then (96, 221) else (81, 213)))) else (if i.val < 958 then (if i.val < 957 then (126, 200) else (53, 23)) else (if i.val < 959 then (16, 177) else (if i.val < 960 then (103, 55) else (39, 0))))) else (if i.val < 966 then (if i.val < 963 then (if i.val < 962 then (74, 131) else (67, 100)) else (if i.val < 964 then (37, 40) else (if i.val < 965 then (125, 137) else (41, 155)))) else (if i.val < 969 then (if i.val < 967 then (137, 93) else (if i.val < 968 then (102, 193) else (99, 221))) else (if i.val < 970 then (139, 246) else (if i.val < 971 then (56, 146) else (27, 137)))))))))) else (if i.val < 1134 then (if i.val < 1053 then (if i.val < 1012 then (if i.val < 992 then (if i.val < 982 then (if i.val < 977 then (if i.val < 974 then (if i.val < 973 then (99, 194) else (87, 19)) else (if i.val < 975 then (129, 227) else (if i.val < 976 then (144, 194) else (17, 142)))) else (if i.val < 979 then (if i.val < 978 then (122, 172) else (91, 180)) else (if i.val < 980 then (83, 251) else (if i.val < 981 then (143, 144) else (129, 55))))) else (if i.val < 987 then (if i.val < 984 then (if i.val < 983 then (17, 191) else (134, 220)) else (if i.val < 985 then (131, 218) else (if i.val < 986 then (93, 53) else (60, 168)))) else (if i.val < 989 then (if i.val < 988 then (120, 170) else (136, 182)) else (if i.val < 990 then (85, 113) else (if i.val < 991 then (88, 5) else (117, 104)))))) else (if i.val < 1002 then (if i.val < 997 then (if i.val < 994 then (if i.val < 993 then (76, 121) else (46, 0)) else (if i.val < 995 then (43, 191) else (if i.val < 996 then (23, 15) else (143, 46)))) else (if i.val < 999 then (if i.val < 998 then (122, 13) else (102, 70)) else (if i.val < 1000 then (40, 195) else (if i.val < 1001 then (70, 117) else (125, 247))))) else (if i.val < 1007 then (if i.val < 1004 then (if i.val < 1003 then (132, 57) else (64, 161)) else (if i.val < 1005 then (136, 98) else (if i.val < 1006 then (112, 171) else (41, 234)))) else (if i.val < 1009 then (if i.val < 1008 then (116, 160) else (133, 224)) else (if i.val < 1010 then (129, 168) else (if i.val < 1011 then (90, 22) else (25, 145))))))) else (if i.val < 1032 then (if i.val < 1022 then (if i.val < 1017 then (if i.val < 1014 then (if i.val < 1013 then (28, 111) else (71, 58)) else (if i.val < 1015 then (10, 137) else (if i.val < 1016 then (72, 219) else (35, 67)))) else (if i.val < 1019 then (if i.val < 1018 then (118, 232) else (113, 180)) else (if i.val < 1020 then (45, 208) else (if i.val < 1021 then (142, 236) else (41, 110))))) else (if i.val < 1027 then (if i.val < 1024 then (if i.val < 1023 then (25, 43) else (87, 48)) else (if i.val < 1025 then (76, 9) else (if i.val < 1026 then (107, 111) else (67, 180)))) else (if i.val < 1029 then (if i.val < 1028 then (137, 14) else (139, 106)) else (if i.val < 1030 then (68, 191) else (if i.val < 1031 then (41, 94) else (123, 105)))))) else (if i.val < 1042 then (if i.val < 1037 then (if i.val < 1034 then (if i.val < 1033 then (56, 143) else (85, 216)) else (if i.val < 1035 then (95, 50) else (if i.val < 1036 then (113, 237) else (115, 90)))) else (if i.val < 1039 then (if i.val < 1038 then (56, 8) else (139, 252)) else (if i.val < 1040 then (63, 224) else (if i.val < 1041 then (112, 6) else (135, 251))))) else (if i.val < 1047 then (if i.val < 1044 then (if i.val < 1043 then (110, 131) else (143, 191)) else (if i.val < 1045 then (142, 221) else (if i.val < 1046 then (143, 159) else (84, 157)))) else (if i.val < 1050 then (if i.val < 1048 then (111, 174) else (if i.val < 1049 then (97, 86) else (101, 98))) else (if i.val < 1051 then (83, 197) else (if i.val < 1052 then (53, 231) else (1, 5)))))))) else (if i.val < 1093 then (if i.val < 1073 then (if i.val < 1063 then (if i.val < 1058 then (if i.val < 1055 then (if i.val < 1054 then (139, 85) else (53, 173)) else (if i.val < 1056 then (139, 56) else (if i.val < 1057 then (96, 235) else (38, 4)))) else (if i.val < 1060 then (if i.val < 1059 then (68, 57) else (120, 206)) else (if i.val < 1061 then (142, 225) else (if i.val < 1062 then (77, 133) else (20, 216))))) else (if i.val < 1068 then (if i.val < 1065 then (if i.val < 1064 then (115, 69) else (93, 237)) else (if i.val < 1066 then (134, 14) else (if i.val < 1067 then (30, 140) else (5, 170)))) else (if i.val < 1070 then (if i.val < 1069 then (122, 197) else (109, 130)) else (if i.val < 1071 then (49, 60) else (if i.val < 1072 then (94, 136) else (92, 167)))))) else (if i.val < 1083 then (if i.val < 1078 then (if i.val < 1075 then (if i.val < 1074 then (11, 27) else (143, 45)) else (if i.val < 1076 then (45, 86) else (if i.val < 1077 then (2, 9) else (75, 174)))) else (if i.val < 1080 then (if i.val < 1079 then (55, 10) else (5, 83)) else (if i.val < 1081 then (83, 223) else (if i.val < 1082 then (14, 212) else (125, 153))))) else (if i.val < 1088 then (if i.val < 1085 then (if i.val < 1084 then (144, 25) else (27, 128)) else (if i.val < 1086 then (138, 126) else (if i.val < 1087 then (114, 214) else (53, 3)))) else (if i.val < 1090 then (if i.val < 1089 then (142, 80) else (0, 98)) else (if i.val < 1091 then (83, 53) else (if i.val < 1092 then (139, 207) else (111, 67))))))) else (if i.val < 1113 then (if i.val < 1103 then (if i.val < 1098 then (if i.val < 1095 then (if i.val < 1094 then (120, 72) else (111, 11)) else (if i.val < 1096 then (135, 0) else (if i.val < 1097 then (43, 184) else (63, 122)))) else (if i.val < 1100 then (if i.val < 1099 then (62, 21) else (91, 29)) else (if i.val < 1101 then (134, 245) else (if i.val < 1102 then (56, 59) else (58, 3))))) else (if i.val < 1108 then (if i.val < 1105 then (if i.val < 1104 then (31, 115) else (56, 132)) else (if i.val < 1106 then (24, 209) else (if i.val < 1107 then (58, 7) else (47, 105)))) else (if i.val < 1110 then (if i.val < 1109 then (9, 50) else (61, 155)) else (if i.val < 1111 then (122, 85) else (if i.val < 1112 then (137, 145) else (127, 181)))))) else (if i.val < 1123 then (if i.val < 1118 then (if i.val < 1115 then (if i.val < 1114 then (109, 53) else (20, 206)) else (if i.val < 1116 then (142, 53) else (if i.val < 1117 then (124, 105) else (31, 4)))) else (if i.val < 1120 then (if i.val < 1119 then (28, 11) else (132, 131)) else (if i.val < 1121 then (59, 27) else (if i.val < 1122 then (85, 78) else (96, 172))))) else (if i.val < 1128 then (if i.val < 1125 then (if i.val < 1124 then (83, 231) else (5, 4)) else (if i.val < 1126 then (142, 113) else (if i.val < 1127 then (119, 199) else (18, 251)))) else (if i.val < 1131 then (if i.val < 1129 then (101, 157) else (if i.val < 1130 then (86, 238) else (4, 252))) else (if i.val < 1132 then (11, 105) else (if i.val < 1133 then (88, 184) else (31, 190))))))))) else (if i.val < 1215 then (if i.val < 1174 then (if i.val < 1154 then (if i.val < 1144 then (if i.val < 1139 then (if i.val < 1136 then (if i.val < 1135 then (130, 137) else (49, 225)) else (if i.val < 1137 then (45, 102) else (if i.val < 1138 then (66, 77) else (105, 27)))) else (if i.val < 1141 then (if i.val < 1140 then (27, 30) else (47, 15)) else (if i.val < 1142 then (67, 188) else (if i.val < 1143 then (51, 32) else (56, 212))))) else (if i.val < 1149 then (if i.val < 1146 then (if i.val < 1145 then (12, 253) else (22, 25)) else (if i.val < 1147 then (74, 210) else (if i.val < 1148 then (79, 77) else (111, 236)))) else (if i.val < 1151 then (if i.val < 1150 then (141, 207) else (130, 249)) else (if i.val < 1152 then (51, 105) else (if i.val < 1153 then (117, 99) else (79, 105)))))) else (if i.val < 1164 then (if i.val < 1159 then (if i.val < 1156 then (if i.val < 1155 then (119, 220) else (108, 242)) else (if i.val < 1157 then (142, 67) else (if i.val < 1158 then (57, 22) else (5, 205)))) else (if i.val < 1161 then (if i.val < 1160 then (6, 90) else (13, 90)) else (if i.val < 1162 then (78, 249) else (if i.val < 1163 then (101, 143) else (69, 214))))) else (if i.val < 1169 then (if i.val < 1166 then (if i.val < 1165 then (95, 156) else (74, 186)) else (if i.val < 1167 then (21, 209) else (if i.val < 1168 then (103, 45) else (56, 124)))) else (if i.val < 1171 then (if i.val < 1170 then (135, 27) else (138, 242)) else (if i.val < 1172 then (45, 70) else (if i.val < 1173 then (94, 51) else (61, 4))))))) else (if i.val < 1194 then (if i.val < 1184 then (if i.val < 1179 then (if i.val < 1176 then (if i.val < 1175 then (46, 1) else (97, 7)) else (if i.val < 1177 then (18, 242) else (if i.val < 1178 then (118, 50) else (108, 160)))) else (if i.val < 1181 then (if i.val < 1180 then (84, 86) else (101, 92)) else (if i.val < 1182 then (137, 180) else (if i.val < 1183 then (17, 163) else (65, 102))))) else (if i.val < 1189 then (if i.val < 1186 then (if i.val < 1185 then (92, 155) else (61, 84)) else (if i.val < 1187 then (14, 187) else (if i.val < 1188 then (14, 213) else (62, 109)))) else (if i.val < 1191 then (if i.val < 1190 then (44, 13) else (45, 162)) else (if i.val < 1192 then (45, 226) else (if i.val < 1193 then (117, 226) else (75, 36)))))) else (if i.val < 1204 then (if i.val < 1199 then (if i.val < 1196 then (if i.val < 1195 then (64, 96) else (118, 142)) else (if i.val < 1197 then (127, 173) else (if i.val < 1198 then (134, 37) else (73, 40)))) else (if i.val < 1201 then (if i.val < 1200 then (132, 17) else (82, 193)) else (if i.val < 1202 then (134, 213) else (if i.val < 1203 then (123, 182) else (127, 97))))) else (if i.val < 1209 then (if i.val < 1206 then (if i.val < 1205 then (120, 219) else (35, 149)) else (if i.val < 1207 then (98, 163) else (if i.val < 1208 then (80, 62) else (33, 244)))) else (if i.val < 1212 then (if i.val < 1210 then (78, 222) else (if i.val < 1211 then (94, 230) else (24, 161))) else (if i.val < 1213 then (35, 126) else (if i.val < 1214 then (68, 183) else (136, 77)))))))) else (if i.val < 1255 then (if i.val < 1235 then (if i.val < 1225 then (if i.val < 1220 then (if i.val < 1217 then (if i.val < 1216 then (114, 55) else (134, 112)) else (if i.val < 1218 then (109, 131) else (if i.val < 1219 then (133, 180) else (129, 45)))) else (if i.val < 1222 then (if i.val < 1221 then (135, 48) else (93, 164)) else (if i.val < 1223 then (142, 56) else (if i.val < 1224 then (18, 17) else (7, 107))))) else (if i.val < 1230 then (if i.val < 1227 then (if i.val < 1226 then (141, 137) else (66, 85)) else (if i.val < 1228 then (24, 130) else (if i.val < 1229 then (38, 132) else (25, 150)))) else (if i.val < 1232 then (if i.val < 1231 then (52, 113) else (96, 156)) else (if i.val < 1233 then (143, 92) else (if i.val < 1234 then (82, 224) else (132, 54)))))) else (if i.val < 1245 then (if i.val < 1240 then (if i.val < 1237 then (if i.val < 1236 then (138, 42) else (90, 109)) else (if i.val < 1238 then (144, 23) else (if i.val < 1239 then (118, 193) else (144, 173)))) else (if i.val < 1242 then (if i.val < 1241 then (35, 248) else (143, 16)) else (if i.val < 1243 then (141, 42) else (if i.val < 1244 then (18, 130) else (49, 88))))) else (if i.val < 1250 then (if i.val < 1247 then (if i.val < 1246 then (88, 194) else (65, 212)) else (if i.val < 1248 then (52, 15) else (if i.val < 1249 then (135, 230) else (101, 230)))) else (if i.val < 1252 then (if i.val < 1251 then (37, 228) else (49, 177)) else (if i.val < 1253 then (122, 223) else (if i.val < 1254 then (34, 90) else (72, 46))))))) else (if i.val < 1275 then (if i.val < 1265 then (if i.val < 1260 then (if i.val < 1257 then (if i.val < 1256 then (126, 37) else (40, 94)) else (if i.val < 1258 then (93, 10) else (if i.val < 1259 then (112, 175) else (125, 100)))) else (if i.val < 1262 then (if i.val < 1261 then (117, 190) else (22, 155)) else (if i.val < 1263 then (93, 196) else (if i.val < 1264 then (103, 230) else (144, 220))))) else (if i.val < 1270 then (if i.val < 1267 then (if i.val < 1266 then (67, 66) else (66, 78)) else (if i.val < 1268 then (142, 104) else (if i.val < 1269 then (42, 244) else (47, 119)))) else (if i.val < 1272 then (if i.val < 1271 then (125, 174) else (57, 173)) else (if i.val < 1273 then (58, 224) else (if i.val < 1274 then (105, 1) else (143, 227)))))) else (if i.val < 1285 then (if i.val < 1280 then (if i.val < 1277 then (if i.val < 1276 then (89, 150) else (81, 195)) else (if i.val < 1278 then (55, 211) else (if i.val < 1279 then (29, 185) else (55, 78)))) else (if i.val < 1282 then (if i.val < 1281 then (21, 194) else (86, 109)) else (if i.val < 1283 then (94, 64) else (if i.val < 1284 then (84, 16) else (22, 54))))) else (if i.val < 1290 then (if i.val < 1287 then (if i.val < 1286 then (2, 163) else (29, 157)) else (if i.val < 1288 then (32, 120) else (if i.val < 1289 then (49, 59) else (39, 19)))) else (if i.val < 1293 then (if i.val < 1291 then (1, 165) else (if i.val < 1292 then (44, 127) else (14, 37))) else (if i.val < 1294 then (50, 170) else (if i.val < 1295 then (32, 139) else (135, 113))))))))))))

def g32p_supplierGroup12_classify : Fin 1296 → Fin 102 :=
  fun i => (if i.val < 648 then (if i.val < 324 then (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 0 else 38) else (if i.val < 3 then 65 else (if i.val < 4 then 75 else 45))) else (if i.val < 7 then (if i.val < 6 then 69 else 34) else (if i.val < 8 then 38 else (if i.val < 9 then 49 else 34)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 96 else 64) else (if i.val < 13 then 18 else (if i.val < 14 then 38 else 64))) else (if i.val < 17 then (if i.val < 16 then 6 else 84) else (if i.val < 18 then 49 else (if i.val < 19 then 18 else 35))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then 38 else 65) else (if i.val < 23 then 21 else (if i.val < 24 then 13 else 65))) else (if i.val < 27 then (if i.val < 26 then 49 else 30) else (if i.val < 28 then 21 else (if i.val < 29 then 21 else 34)))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then 38 else 49) else (if i.val < 33 then 13 else (if i.val < 34 then 21 else 57))) else (if i.val < 37 then (if i.val < 36 then 65 else 49) else (if i.val < 38 then 34 else (if i.val < 39 then 21 else 18)))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then 84 else 35) else (if i.val < 43 then 30 else (if i.val < 44 then 89 else 77))) else (if i.val < 47 then (if i.val < 46 then 21 else 82) else (if i.val < 48 then 21 else (if i.val < 49 then 30 else 38)))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then 49 else 34) else (if i.val < 53 then 89 else (if i.val < 54 then 77 else 38))) else (if i.val < 57 then (if i.val < 56 then 89 else 99) else (if i.val < 58 then 100 else (if i.val < 59 then 49 else 77))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then 88 else 13) else (if i.val < 63 then 21 else (if i.val < 64 then 49 else 57))) else (if i.val < 67 then (if i.val < 66 then 21 else 82) else (if i.val < 68 then 57 else (if i.val < 69 then 82 else 38)))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then 49 else 34) else (if i.val < 73 then 13 else (if i.val < 74 then 3 else 40))) else (if i.val < 78 then (if i.val < 76 then 38 else (if i.val < 77 then 89 else 21)) else (if i.val < 79 then 46 else (if i.val < 80 then 49 else 71))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then 34 else 34) else (if i.val < 84 then 97 else (if i.val < 85 then 91 else 18))) else (if i.val < 88 then (if i.val < 87 then 69 else 49) else (if i.val < 89 then 57 else (if i.val < 90 then 3 else 30)))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then 69 else 40) else (if i.val < 94 then 46 else (if i.val < 95 then 38 else 91))) else (if i.val < 98 then (if i.val < 97 then 69 else 46) else (if i.val < 99 then 30 else (if i.val < 100 then 21 else 21))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then 34 else 38) else (if i.val < 104 then 49 else (if i.val < 105 then 46 else 21))) else (if i.val < 108 then (if i.val < 107 then 57 else 49) else (if i.val < 109 then 18 else (if i.val < 110 then 46 else 34)))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then 71 else 13) else (if i.val < 114 then 34 else (if i.val < 115 then 46 else 13))) else (if i.val < 118 then (if i.val < 117 then 89 else 71) else (if i.val < 119 then 69 else (if i.val < 120 then 49 else 57)))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then 91 else 49) else (if i.val < 124 then 34 else (if i.val < 125 then 21 else 18))) else (if i.val < 128 then (if i.val < 127 then 57 else 46) else (if i.val < 129 then 101 else (if i.val < 130 then 49 else 45)))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then 32 else 57) else (if i.val < 134 then 6 else (if i.val < 135 then 3 else 49))) else (if i.val < 138 then (if i.val < 137 then 30 else 21) else (if i.val < 139 then 30 else (if i.val < 140 then 45 else 23))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then 69 else 32) else (if i.val < 144 then 8 else (if i.val < 145 then 40 else 57))) else (if i.val < 148 then (if i.val < 147 then 21 else 13) else (if i.val < 149 then 46 else (if i.val < 150 then 6 else 38)))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then 3 else 21) else (if i.val < 154 then 46 else (if i.val < 155 then 91 else 30))) else (if i.val < 159 then (if i.val < 157 then 69 else (if i.val < 158 then 69 else 30)) else (if i.val < 160 then 38 else (if i.val < 161 then 49 else 46)))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then 21 else 57) else (if i.val < 165 then 89 else (if i.val < 166 then 49 else 21))) else (if i.val < 169 then (if i.val < 168 then 30 else 65) else (if i.val < 170 then 23 else (if i.val < 171 then 21 else 8)))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then 21 else 30) else (if i.val < 175 then 38 else (if i.val < 176 then 49 else 34))) else (if i.val < 179 then (if i.val < 178 then 65 else 23) else (if i.val < 180 then 6 else (if i.val < 181 then 84 else 49))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then 35 else 69) else (if i.val < 185 then 57 else (if i.val < 186 then 21 else 8))) else (if i.val < 189 then (if i.val < 188 then 57 else 49) else (if i.val < 190 then 46 else (if i.val < 191 then 34 else 18)))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then 69 else 46) else (if i.val < 195 then 46 else (if i.val < 196 then 21 else 49))) else (if i.val < 199 then (if i.val < 198 then 57 else 34) else (if i.val < 200 then 13 else (if i.val < 201 then 38 else 57)))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then 21 else 46) else (if i.val < 205 then 13 else (if i.val < 206 then 65 else 34))) else (if i.val < 209 then (if i.val < 208 then 46 else 57) else (if i.val < 210 then 38 else (if i.val < 211 then 46 else 65)))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then 6 else 30) else (if i.val < 215 then 38 else (if i.val < 216 then 84 else 21))) else (if i.val < 219 then (if i.val < 218 then 49 else 30) else (if i.val < 220 then 21 else (if i.val < 221 then 18 else 46))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then 34 else 91) else (if i.val < 225 then 23 else (if i.val < 226 then 21 else 10))) else (if i.val < 229 then (if i.val < 228 then 6 else 34) else (if i.val < 230 then 38 else (if i.val < 231 then 49 else 29)))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then 74 else 38) else (if i.val < 235 then 64 else (if i.val < 236 then 69 else 46))) else (if i.val < 240 then (if i.val < 238 then 49 else (if i.val < 239 then 79 else 30)) else (if i.val < 241 then 84 else (if i.val < 242 then 49 else 57))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then 21 else 82) else (if i.val < 246 then 86 else (if i.val < 247 then 49 else 21))) else (if i.val < 250 then (if i.val < 249 then 18 else 45) else (if i.val < 251 then 32 else (if i.val < 252 then 30 else 45)))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then 3 else 19) else (if i.val < 256 then 21 else (if i.val < 257 then 32 else 82))) else (if i.val < 260 then (if i.val < 259 then 57 else 46) else (if i.val < 261 then 49 else (if i.val < 262 then 57 else 34))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then 38 else 34) else (if i.val < 266 then 45 else (if i.val < 267 then 66 else 79))) else (if i.val < 270 then (if i.val < 269 then 91 else 49) else (if i.val < 271 then 21 else (if i.val < 272 then 57 else 46)))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then 21 else 32) else (if i.val < 276 then 77 else (if i.val < 277 then 86 else 10))) else (if i.val < 280 then (if i.val < 279 then 38 else 6) else (if i.val < 281 then 30 else (if i.val < 282 then 38 else 49)))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then 34 else 66) else (if i.val < 286 then 77 else (if i.val < 287 then 38 else 65))) else (if i.val < 290 then (if i.val < 289 then 21 else 13) else (if i.val < 291 then 49 else (if i.val < 292 then 43 else 30)))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then 29 else 30) else (if i.val < 296 then 69 else (if i.val < 297 then 74 else 46))) else (if i.val < 300 then (if i.val < 299 then 38 else 21) else (if i.val < 301 then 46 else (if i.val < 302 then 30 else 21))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then 38 else 49) else (if i.val < 306 then 46 else (if i.val < 307 then 57 else 19))) else (if i.val < 310 then (if i.val < 309 then 30 else 79) else (if i.val < 311 then 13 else (if i.val < 312 then 30 else 84)))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then 49 else 57) else (if i.val < 316 then 21 else (if i.val < 317 then 79 else 86))) else (if i.val < 321 then (if i.val < 319 then 23 else (if i.val < 320 then 46 else 30)) else (if i.val < 322 then 57 else (if i.val < 323 then 10 else 69))))))))) else (if i.val < 486 then (if i.val < 405 then (if i.val < 364 then (if i.val < 344 then (if i.val < 334 then (if i.val < 329 then (if i.val < 326 then (if i.val < 325 then 32 else 43) else (if i.val < 327 then 10 else (if i.val < 328 then 82 else 30))) else (if i.val < 331 then (if i.val < 330 then 82 else 30) else (if i.val < 332 then 69 else (if i.val < 333 then 86 else 30)))) else (if i.val < 339 then (if i.val < 336 then (if i.val < 335 then 18 else 46) else (if i.val < 337 then 34 else (if i.val < 338 then 34 else 46))) else (if i.val < 341 then (if i.val < 340 then 64 else 79) else (if i.val < 342 then 34 else (if i.val < 343 then 86 else 69))))) else (if i.val < 354 then (if i.val < 349 then (if i.val < 346 then (if i.val < 345 then 46 else 45) else (if i.val < 347 then 49 else (if i.val < 348 then 57 else 38))) else (if i.val < 351 then (if i.val < 350 then 30 else 46) else (if i.val < 352 then 65 else (if i.val < 353 then 43 else 49)))) else (if i.val < 359 then (if i.val < 356 then (if i.val < 355 then 57 else 49) else (if i.val < 357 then 21 else (if i.val < 358 then 19 else 57))) else (if i.val < 361 then (if i.val < 360 then 46 else 34) else (if i.val < 362 then 23 else (if i.val < 363 then 10 else 82)))))) else (if i.val < 384 then (if i.val < 374 then (if i.val < 369 then (if i.val < 366 then (if i.val < 365 then 46 else 21) else (if i.val < 367 then 49 else (if i.val < 368 then 57 else 49))) else (if i.val < 371 then (if i.val < 370 then 2 else 57) else (if i.val < 372 then 44 else (if i.val < 373 then 46 else 57)))) else (if i.val < 379 then (if i.val < 376 then (if i.val < 375 then 38 else 34) else (if i.val < 377 then 46 else (if i.val < 378 then 29 else 74))) else (if i.val < 381 then (if i.val < 380 then 49 else 57) else (if i.val < 382 then 66 else (if i.val < 383 then 30 else 21))))) else (if i.val < 394 then (if i.val < 389 then (if i.val < 386 then (if i.val < 385 then 79 else 57) else (if i.val < 387 then 13 else (if i.val < 388 then 49 else 30))) else (if i.val < 391 then (if i.val < 390 then 69 else 49) else (if i.val < 392 then 35 else (if i.val < 393 then 21 else 51)))) else (if i.val < 399 then (if i.val < 396 then (if i.val < 395 then 57 else 46) else (if i.val < 397 then 57 else (if i.val < 398 then 75 else 46))) else (if i.val < 402 then (if i.val < 400 then 21 else (if i.val < 401 then 74 else 82)) else (if i.val < 403 then 57 else (if i.val < 404 then 38 else 77))))))) else (if i.val < 445 then (if i.val < 425 then (if i.val < 415 then (if i.val < 410 then (if i.val < 407 then (if i.val < 406 then 57 else 21) else (if i.val < 408 then 13 else (if i.val < 409 then 86 else 38))) else (if i.val < 412 then (if i.val < 411 then 30 else 10) else (if i.val < 413 then 46 else (if i.val < 414 then 30 else 38)))) else (if i.val < 420 then (if i.val < 417 then (if i.val < 416 then 45 else 30) else (if i.val < 418 then 91 else (if i.val < 419 then 38 else 29))) else (if i.val < 422 then (if i.val < 421 then 69 else 46) else (if i.val < 423 then 49 else (if i.val < 424 then 74 else 30))))) else (if i.val < 435 then (if i.val < 430 then (if i.val < 427 then (if i.val < 426 then 3 else 19) else (if i.val < 428 then 66 else (if i.val < 429 then 34 else 77))) else (if i.val < 432 then (if i.val < 431 then 46 else 38) else (if i.val < 433 then 66 else (if i.val < 434 then 21 else 30)))) else (if i.val < 440 then (if i.val < 437 then (if i.val < 436 then 69 else 21) else (if i.val < 438 then 30 else (if i.val < 439 then 38 else 49))) else (if i.val < 442 then (if i.val < 441 then 13 else 21) else (if i.val < 443 then 57 else (if i.val < 444 then 49 else 79)))))) else (if i.val < 465 then (if i.val < 455 then (if i.val < 450 then (if i.val < 447 then (if i.val < 446 then 46 else 30) else (if i.val < 448 then 43 else (if i.val < 449 then 46 else 30))) else (if i.val < 452 then (if i.val < 451 then 13 else 64) else (if i.val < 453 then 79 else (if i.val < 454 then 57 else 23)))) else (if i.val < 460 then (if i.val < 457 then (if i.val < 456 then 57 else 46) else (if i.val < 458 then 29 else (if i.val < 459 then 49 else 21))) else (if i.val < 462 then (if i.val < 461 then 30 else 69) else (if i.val < 463 then 51 else (if i.val < 464 then 57 else 13))))) else (if i.val < 475 then (if i.val < 470 then (if i.val < 467 then (if i.val < 466 then 46 else 38) else (if i.val < 468 then 69 else (if i.val < 469 then 46 else 3))) else (if i.val < 472 then (if i.val < 471 then 34 else 21) else (if i.val < 473 then 21 else (if i.val < 474 then 30 else 49)))) else (if i.val < 480 then (if i.val < 477 then (if i.val < 476 then 46 else 69) else (if i.val < 478 then 57 else (if i.val < 479 then 64 else 49))) else (if i.val < 483 then (if i.val < 481 then 21 else (if i.val < 482 then 30 else 91)) else (if i.val < 484 then 21 else (if i.val < 485 then 51 else 75)))))))) else (if i.val < 567 then (if i.val < 526 then (if i.val < 506 then (if i.val < 496 then (if i.val < 491 then (if i.val < 488 then (if i.val < 487 then 49 else 21) else (if i.val < 489 then 57 else (if i.val < 490 then 57 else 19))) else (if i.val < 493 then (if i.val < 492 then 46 else 46) else (if i.val < 494 then 38 else (if i.val < 495 then 57 else 46)))) else (if i.val < 501 then (if i.val < 498 then (if i.val < 497 then 13 else 64) else (if i.val < 499 then 30 else (if i.val < 500 then 46 else 38))) else (if i.val < 503 then (if i.val < 502 then 49 else 57) else (if i.val < 504 then 49 else (if i.val < 505 then 30 else 21))))) else (if i.val < 516 then (if i.val < 511 then (if i.val < 508 then (if i.val < 507 then 79 else 21) else (if i.val < 509 then 46 else (if i.val < 510 then 86 else 34))) else (if i.val < 513 then (if i.val < 512 then 13 else 30) else (if i.val < 514 then 69 else (if i.val < 515 then 46 else 46)))) else (if i.val < 521 then (if i.val < 518 then (if i.val < 517 then 21 else 57) else (if i.val < 519 then 30 else (if i.val < 520 then 13 else 38))) else (if i.val < 523 then (if i.val < 522 then 57 else 69) else (if i.val < 524 then 10 else (if i.val < 525 then 30 else 69)))))) else (if i.val < 546 then (if i.val < 536 then (if i.val < 531 then (if i.val < 528 then (if i.val < 527 then 30 else 57) else (if i.val < 529 then 38 else (if i.val < 530 then 57 else 21))) else (if i.val < 533 then (if i.val < 532 then 46 else 38) else (if i.val < 534 then 34 else (if i.val < 535 then 13 else 30)))) else (if i.val < 541 then (if i.val < 538 then (if i.val < 537 then 30 else 69) else (if i.val < 539 then 82 else (if i.val < 540 then 46 else 34))) else (if i.val < 543 then (if i.val < 542 then 30 else 46) else (if i.val < 544 then 57 else (if i.val < 545 then 38 else 69))))) else (if i.val < 556 then (if i.val < 551 then (if i.val < 548 then (if i.val < 547 then 49 else 46) else (if i.val < 549 then 34 else (if i.val < 550 then 38 else 3))) else (if i.val < 553 then (if i.val < 552 then 75 else 100) else (if i.val < 554 then 30 else (if i.val < 555 then 21 else 75)))) else (if i.val < 561 then (if i.val < 558 then (if i.val < 557 then 30 else 38) else (if i.val < 559 then 49 else (if i.val < 560 then 45 else 92))) else (if i.val < 564 then (if i.val < 562 then 18 else (if i.val < 563 then 69 else 57)) else (if i.val < 565 then 89 else (if i.val < 566 then 49 else 30))))))) else (if i.val < 607 then (if i.val < 587 then (if i.val < 577 then (if i.val < 572 then (if i.val < 569 then (if i.val < 568 then 69 else 71) else (if i.val < 570 then 57 else (if i.val < 571 then 46 else 49))) else (if i.val < 574 then (if i.val < 573 then 46 else 91) else (if i.val < 575 then 49 else (if i.val < 576 then 30 else 21)))) else (if i.val < 582 then (if i.val < 579 then (if i.val < 578 then 34 else 43) else (if i.val < 580 then 25 else (if i.val < 581 then 57 else 46))) else (if i.val < 584 then (if i.val < 583 then 46 else 38) else (if i.val < 585 then 64 else (if i.val < 586 then 24 else 1))))) else (if i.val < 597 then (if i.val < 592 then (if i.val < 589 then (if i.val < 588 then 3 else 75) else (if i.val < 590 then 38 else (if i.val < 591 then 49 else 100))) else (if i.val < 594 then (if i.val < 593 then 77 else 85) else (if i.val < 595 then 75 else (if i.val < 596 then 38 else 15)))) else (if i.val < 602 then (if i.val < 599 then (if i.val < 598 then 21 else 13) else (if i.val < 600 then 49 else (if i.val < 601 then 30 else 21))) else (if i.val < 604 then (if i.val < 603 then 69 else 51) else (if i.val < 605 then 57 else (if i.val < 606 then 49 else 1)))))) else (if i.val < 627 then (if i.val < 617 then (if i.val < 612 then (if i.val < 609 then (if i.val < 608 then 37 else 69) else (if i.val < 610 then 49 else (if i.val < 611 then 92 else 46))) else (if i.val < 614 then (if i.val < 613 then 57 else 21) else (if i.val < 615 then 13 else (if i.val < 616 then 13 else 15)))) else (if i.val < 622 then (if i.val < 619 then (if i.val < 618 then 46 else 69) else (if i.val < 620 then 49 else (if i.val < 621 then 57 else 57))) else (if i.val < 624 then (if i.val < 623 then 46 else 49) else (if i.val < 625 then 84 else (if i.val < 626 then 35 else 75))))) else (if i.val < 637 then (if i.val < 632 then (if i.val < 629 then (if i.val < 628 then 89 else 49) else (if i.val < 630 then 21 else (if i.val < 631 then 28 else 87))) else (if i.val < 634 then (if i.val < 633 then 84 else 79) else (if i.val < 635 then 69 else (if i.val < 636 then 35 else 81)))) else (if i.val < 642 then (if i.val < 639 then (if i.val < 638 then 57 else 13) else (if i.val < 640 then 46 else (if i.val < 641 then 49 else 19))) else (if i.val < 645 then (if i.val < 643 then 13 else (if i.val < 644 then 57 else 30)) else (if i.val < 646 then 38 else (if i.val < 647 then 82 else 91)))))))))) else (if i.val < 972 then (if i.val < 810 then (if i.val < 729 then (if i.val < 688 then (if i.val < 668 then (if i.val < 658 then (if i.val < 653 then (if i.val < 650 then (if i.val < 649 then 49 else 34) else (if i.val < 651 then 21 else (if i.val < 652 then 56 else 35))) else (if i.val < 655 then (if i.val < 654 then 30 else 29) else (if i.val < 656 then 71 else (if i.val < 657 then 2 else 85)))) else (if i.val < 663 then (if i.val < 660 then (if i.val < 659 then 84 else 59) else (if i.val < 661 then 19 else (if i.val < 662 then 57 else 43))) else (if i.val < 665 then (if i.val < 664 then 13 else 38) else (if i.val < 666 then 25 else (if i.val < 667 then 18 else 21))))) else (if i.val < 678 then (if i.val < 673 then (if i.val < 670 then (if i.val < 669 then 13 else 35) else (if i.val < 671 then 24 else (if i.val < 672 then 69 else 35))) else (if i.val < 675 then (if i.val < 674 then 74 else 8) else (if i.val < 676 then 46 else (if i.val < 677 then 24 else 15)))) else (if i.val < 683 then (if i.val < 680 then (if i.val < 679 then 46 else 50) else (if i.val < 681 then 49 else (if i.val < 682 then 64 else 30))) else (if i.val < 685 then (if i.val < 684 then 24 else 34) else (if i.val < 686 then 38 else (if i.val < 687 then 49 else 1)))))) else (if i.val < 708 then (if i.val < 698 then (if i.val < 693 then (if i.val < 690 then (if i.val < 689 then 21 else 30) else (if i.val < 691 then 21 else (if i.val < 692 then 34 else 59))) else (if i.val < 695 then (if i.val < 694 then 21 else 50) else (if i.val < 696 then 75 else (if i.val < 697 then 30 else 38)))) else (if i.val < 703 then (if i.val < 700 then (if i.val < 699 then 3 else 40) else (if i.val < 701 then 38 else (if i.val < 702 then 89 else 21))) else (if i.val < 705 then (if i.val < 704 then 49 else 71) else (if i.val < 706 then 34 else (if i.val < 707 then 49 else 57))))) else (if i.val < 718 then (if i.val < 713 then (if i.val < 710 then (if i.val < 709 then 81 else 8) else (if i.val < 711 then 30 else (if i.val < 712 then 28 else 43))) else (if i.val < 715 then (if i.val < 714 then 66 else 46) else (if i.val < 716 then 87 else (if i.val < 717 then 25 else 85)))) else (if i.val < 723 then (if i.val < 720 then (if i.val < 719 then 38 else 49) else (if i.val < 721 then 38 else (if i.val < 722 then 91 else 46))) else (if i.val < 726 then (if i.val < 724 then 30 else (if i.val < 725 then 15 else 30)) else (if i.val < 727 then 19 else (if i.val < 728 then 46 else 38))))))) else (if i.val < 769 then (if i.val < 749 then (if i.val < 739 then (if i.val < 734 then (if i.val < 731 then (if i.val < 730 then 13 else 30) else (if i.val < 732 then 30 else (if i.val < 733 then 21 else 8))) else (if i.val < 736 then (if i.val < 735 then 50 else 21) else (if i.val < 737 then 35 else (if i.val < 738 then 85 else 30)))) else (if i.val < 744 then (if i.val < 741 then (if i.val < 740 then 57 else 81) else (if i.val < 742 then 21 else (if i.val < 743 then 100 else 92))) else (if i.val < 746 then (if i.val < 745 then 1 else 40) else (if i.val < 747 then 21 else (if i.val < 748 then 19 else 51))))) else (if i.val < 759 then (if i.val < 754 then (if i.val < 751 then (if i.val < 750 then 13 else 66) else (if i.val < 752 then 43 else (if i.val < 753 then 25 else 49))) else (if i.val < 756 then (if i.val < 755 then 77 else 30) else (if i.val < 757 then 85 else (if i.val < 758 then 92 else 46)))) else (if i.val < 764 then (if i.val < 761 then (if i.val < 760 then 65 else 15) else (if i.val < 762 then 2 else (if i.val < 763 then 24 else 2))) else (if i.val < 766 then (if i.val < 765 then 23 else 50) else (if i.val < 767 then 24 else (if i.val < 768 then 66 else 81)))))) else (if i.val < 789 then (if i.val < 779 then (if i.val < 774 then (if i.val < 771 then (if i.val < 770 then 15 else 46) else (if i.val < 772 then 85 else (if i.val < 773 then 15 else 51))) else (if i.val < 776 then (if i.val < 775 then 30 else 21) else (if i.val < 777 then 8 else (if i.val < 778 then 15 else 34)))) else (if i.val < 784 then (if i.val < 781 then (if i.val < 780 then 23 else 30) else (if i.val < 782 then 69 else (if i.val < 783 then 64 else 49))) else (if i.val < 786 then (if i.val < 785 then 46 else 30) else (if i.val < 787 then 34 else (if i.val < 788 then 46 else 43))))) else (if i.val < 799 then (if i.val < 794 then (if i.val < 791 then (if i.val < 790 then 21 else 25) else (if i.val < 792 then 57 else (if i.val < 793 then 69 else 19))) else (if i.val < 796 then (if i.val < 795 then 46 else 82) else (if i.val < 797 then 84 else (if i.val < 798 then 21 else 57)))) else (if i.val < 804 then (if i.val < 801 then (if i.val < 800 then 38 else 34) else (if i.val < 802 then 21 else (if i.val < 803 then 13 else 13))) else (if i.val < 807 then (if i.val < 805 then 89 else (if i.val < 806 then 71 else 21)) else (if i.val < 808 then 30 else (if i.val < 809 then 8 else 28)))))))) else (if i.val < 891 then (if i.val < 850 then (if i.val < 830 then (if i.val < 820 then (if i.val < 815 then (if i.val < 812 then (if i.val < 811 then 49 else 57) else (if i.val < 813 then 87 else (if i.val < 814 then 49 else 57))) else (if i.val < 817 then (if i.val < 816 then 46 else 50) else (if i.val < 818 then 81 else (if i.val < 819 then 30 else 30)))) else (if i.val < 825 then (if i.val < 822 then (if i.val < 821 then 77 else 85) else (if i.val < 823 then 69 else (if i.val < 824 then 15 else 69))) else (if i.val < 827 then (if i.val < 826 then 51 else 66) else (if i.val < 828 then 46 else (if i.val < 829 then 49 else 57))))) else (if i.val < 840 then (if i.val < 835 then (if i.val < 832 then (if i.val < 831 then 30 else 38) else (if i.val < 833 then 49 else (if i.val < 834 then 57 else 57))) else (if i.val < 837 then (if i.val < 836 then 13 else 38) else (if i.val < 838 then 57 else (if i.val < 839 then 38 else 49)))) else (if i.val < 845 then (if i.val < 842 then (if i.val < 841 then 46 else 34) else (if i.val < 843 then 19 else (if i.val < 844 then 21 else 51))) else (if i.val < 847 then (if i.val < 846 then 56 else 49) else (if i.val < 848 then 13 else (if i.val < 849 then 29 else 21)))))) else (if i.val < 870 then (if i.val < 860 then (if i.val < 855 then (if i.val < 852 then (if i.val < 851 then 71 else 13) else (if i.val < 853 then 21 else (if i.val < 854 then 30 else 25))) else (if i.val < 857 then (if i.val < 856 then 38 else 85) else (if i.val < 858 then 49 else (if i.val < 859 then 57 else 59)))) else (if i.val < 865 then (if i.val < 862 then (if i.val < 861 then 69 else 57) else (if i.val < 863 then 46 else (if i.val < 864 then 57 else 57))) else (if i.val < 867 then (if i.val < 866 then 67 else 57) else (if i.val < 868 then 46 else (if i.val < 869 then 13 else 38))))) else (if i.val < 880 then (if i.val < 875 then (if i.val < 872 then (if i.val < 871 then 38 else 30) else (if i.val < 873 then 38 else (if i.val < 874 then 98 else 25))) else (if i.val < 877 then (if i.val < 876 then 38 else 21) else (if i.val < 878 then 13 else (if i.val < 879 then 21 else 51)))) else (if i.val < 885 then (if i.val < 882 then (if i.val < 881 then 57 else 49) else (if i.val < 883 then 40 else (if i.val < 884 then 81 else 57))) else (if i.val < 888 then (if i.val < 886 then 57 else (if i.val < 887 then 13 else 8)) else (if i.val < 889 then 38 else (if i.val < 890 then 30 else 46))))))) else (if i.val < 931 then (if i.val < 911 then (if i.val < 901 then (if i.val < 896 then (if i.val < 893 then (if i.val < 892 then 65 else 15) else (if i.val < 894 then 50 else (if i.val < 895 then 38 else 46))) else (if i.val < 898 then (if i.val < 897 then 30 else 66) else (if i.val < 899 then 69 else (if i.val < 900 then 38 else 49)))) else (if i.val < 906 then (if i.val < 903 then (if i.val < 902 then 30 else 30) else (if i.val < 904 then 34 else (if i.val < 905 then 38 else 21))) else (if i.val < 908 then (if i.val < 907 then 13 else 49) else (if i.val < 909 then 30 else (if i.val < 910 then 79 else 34))))) else (if i.val < 921 then (if i.val < 916 then (if i.val < 913 then (if i.val < 912 then 29 else 71) else (if i.val < 914 then 59 else (if i.val < 915 then 49 else 74))) else (if i.val < 918 then (if i.val < 917 then 8 else 59) else (if i.val < 919 then 21 else (if i.val < 920 then 3 else 40)))) else (if i.val < 926 then (if i.val < 923 then (if i.val < 922 then 30 else 69) else (if i.val < 924 then 38 else (if i.val < 925 then 49 else 57))) else (if i.val < 928 then (if i.val < 927 then 71 else 34) else (if i.val < 929 then 13 else (if i.val < 930 then 30 else 57)))))) else (if i.val < 951 then (if i.val < 941 then (if i.val < 936 then (if i.val < 933 then (if i.val < 932 then 25 else 23) else (if i.val < 934 then 50 else (if i.val < 935 then 81 else 30))) else (if i.val < 938 then (if i.val < 937 then 21 else 30) else (if i.val < 939 then 30 else (if i.val < 940 then 46 else 43)))) else (if i.val < 946 then (if i.val < 943 then (if i.val < 942 then 85 else 30) else (if i.val < 944 then 57 else (if i.val < 945 then 57 else 13))) else (if i.val < 948 then (if i.val < 947 then 49 else 69) else (if i.val < 949 then 57 else (if i.val < 950 then 46 else 46))))) else (if i.val < 961 then (if i.val < 956 then (if i.val < 953 then (if i.val < 952 then 38 else 30) else (if i.val < 954 then 38 else (if i.val < 955 then 21 else 79))) else (if i.val < 958 then (if i.val < 957 then 29 else 74) else (if i.val < 959 then 13 else (if i.val < 960 then 59 else 21)))) else (if i.val < 966 then (if i.val < 963 then (if i.val < 962 then 46 else 69) else (if i.val < 964 then 57 else (if i.val < 965 then 30 else 23))) else (if i.val < 969 then (if i.val < 967 then 46 else (if i.val < 968 then 30 else 46)) else (if i.val < 970 then 57 else (if i.val < 971 then 77 else 57))))))))) else (if i.val < 1134 then (if i.val < 1053 then (if i.val < 1012 then (if i.val < 992 then (if i.val < 982 then (if i.val < 977 then (if i.val < 974 then (if i.val < 973 then 46 else 49) else (if i.val < 975 then 21 else (if i.val < 976 then 57 else 13))) else (if i.val < 979 then (if i.val < 978 then 46 else 57) else (if i.val < 980 then 13 else (if i.val < 981 then 46 else 38)))) else (if i.val < 987 then (if i.val < 984 then (if i.val < 983 then 13 else 38) else (if i.val < 985 then 30 else (if i.val < 986 then 21 else 30))) else (if i.val < 989 then (if i.val < 988 then 21 else 49) else (if i.val < 990 then 21 else (if i.val < 991 then 46 else 19))))) else (if i.val < 1002 then (if i.val < 997 then (if i.val < 994 then (if i.val < 993 then 57 else 13) else (if i.val < 995 then 13 else (if i.val < 996 then 43 else 21))) else (if i.val < 999 then (if i.val < 998 then 46 else 25) else (if i.val < 1000 then 69 else (if i.val < 1001 then 46 else 30)))) else (if i.val < 1007 then (if i.val < 1004 then (if i.val < 1003 then 38 else 21) else (if i.val < 1005 then 21 else (if i.val < 1006 then 21 else 69))) else (if i.val < 1009 then (if i.val < 1008 then 57 else 57) else (if i.val < 1010 then 38 else (if i.val < 1011 then 57 else 46)))))) else (if i.val < 1032 then (if i.val < 1022 then (if i.val < 1017 then (if i.val < 1014 then (if i.val < 1013 then 34 else 13) else (if i.val < 1015 then 69 else (if i.val < 1016 then 46 else 13))) else (if i.val < 1019 then (if i.val < 1018 then 21 else 46) else (if i.val < 1020 then 46 else (if i.val < 1021 then 38 else 21)))) else (if i.val < 1027 then (if i.val < 1024 then (if i.val < 1023 then 13 else 46) else (if i.val < 1025 then 34 else (if i.val < 1026 then 21 else 21))) else (if i.val < 1029 then (if i.val < 1028 then 49 else 30) else (if i.val < 1030 then 38 else (if i.val < 1031 then 67 else 49))))) else (if i.val < 1042 then (if i.val < 1037 then (if i.val < 1034 then (if i.val < 1033 then 76 else 30) else (if i.val < 1035 then 38 else (if i.val < 1036 then 49 else 57))) else (if i.val < 1039 then (if i.val < 1038 then 98 else 57) else (if i.val < 1040 then 34 else (if i.val < 1041 then 10 else 38)))) else (if i.val < 1047 then (if i.val < 1044 then (if i.val < 1043 then 84 else 49) else (if i.val < 1045 then 57 else (if i.val < 1046 then 49 else 46))) else (if i.val < 1050 then (if i.val < 1048 then 35 else (if i.val < 1049 then 10 else 86)) else (if i.val < 1051 then 45 else (if i.val < 1052 then 69 else 49))))))) else (if i.val < 1093 then (if i.val < 1073 then (if i.val < 1063 then (if i.val < 1058 then (if i.val < 1055 then (if i.val < 1054 then 30 else 69) else (if i.val < 1056 then 57 else (if i.val < 1057 then 49 else 30))) else (if i.val < 1060 then (if i.val < 1059 then 38 else 10) else (if i.val < 1061 then 38 else (if i.val < 1062 then 34 else 34)))) else (if i.val < 1068 then (if i.val < 1065 then (if i.val < 1064 then 59 else 38) else (if i.val < 1066 then 59 else (if i.val < 1067 then 78 else 98))) else (if i.val < 1070 then (if i.val < 1069 then 49 else 77) else (if i.val < 1071 then 29 else (if i.val < 1072 then 38 else 6))))) else (if i.val < 1083 then (if i.val < 1078 then (if i.val < 1075 then (if i.val < 1074 then 67 else 38) else (if i.val < 1076 then 56 else (if i.val < 1077 then 28 else 4))) else (if i.val < 1080 then (if i.val < 1079 then 81 else 78) else (if i.val < 1081 then 84 else (if i.val < 1082 then 76 else 59)))) else (if i.val < 1088 then (if i.val < 1085 then (if i.val < 1084 then 57 else 87) else (if i.val < 1086 then 46 else (if i.val < 1087 then 57 else 69))) else (if i.val < 1090 then (if i.val < 1089 then 46 else 98) else (if i.val < 1091 then 21 else (if i.val < 1092 then 57 else 86)))))) else (if i.val < 1113 then (if i.val < 1103 then (if i.val < 1098 then (if i.val < 1095 then (if i.val < 1094 then 38 else 46) else (if i.val < 1096 then 38 else (if i.val < 1097 then 46 else 30))) else (if i.val < 1100 then (if i.val < 1099 then 30 else 57) else (if i.val < 1101 then 38 else (if i.val < 1102 then 35 else 38)))) else (if i.val < 1108 then (if i.val < 1105 then (if i.val < 1104 then 93 else 76) else (if i.val < 1106 then 49 else (if i.val < 1107 then 23 else 13))) else (if i.val < 1110 then (if i.val < 1109 then 32 else 32) else (if i.val < 1111 then 85 else (if i.val < 1112 then 46 else 30))))) else (if i.val < 1123 then (if i.val < 1118 then (if i.val < 1115 then (if i.val < 1114 then 38 else 30) else (if i.val < 1116 then 49 else (if i.val < 1117 then 46 else 81))) else (if i.val < 1120 then (if i.val < 1119 then 59 else 49) else (if i.val < 1121 then 11 else (if i.val < 1122 then 30 else 6)))) else (if i.val < 1128 then (if i.val < 1125 then (if i.val < 1124 then 11 else 88) else (if i.val < 1126 then 30 else (if i.val < 1127 then 74 else 32))) else (if i.val < 1131 then (if i.val < 1129 then 81 else (if i.val < 1130 then 38 else 93)) else (if i.val < 1132 then 50 else (if i.val < 1133 then 49 else 76)))))))) else (if i.val < 1215 then (if i.val < 1174 then (if i.val < 1154 then (if i.val < 1144 then (if i.val < 1139 then (if i.val < 1136 then (if i.val < 1135 then 86 else 88) else (if i.val < 1137 then 56 else (if i.val < 1138 then 69 else 92))) else (if i.val < 1141 then (if i.val < 1140 then 88 else 25) else (if i.val < 1142 then 6 else (if i.val < 1143 then 64 else 10)))) else (if i.val < 1149 then (if i.val < 1146 then (if i.val < 1145 then 34 else 67) else (if i.val < 1147 then 51 else (if i.val < 1148 then 29 else 78))) else (if i.val < 1151 then (if i.val < 1150 then 38 else 49) else (if i.val < 1152 then 66 else (if i.val < 1153 then 21 else 30))))) else (if i.val < 1164 then (if i.val < 1159 then (if i.val < 1156 then (if i.val < 1155 then 38 else 74) else (if i.val < 1157 then 49 else (if i.val < 1158 then 4 else 13))) else (if i.val < 1161 then (if i.val < 1160 then 3 else 92) else (if i.val < 1162 then 93 else (if i.val < 1163 then 50 else 45)))) else (if i.val < 1169 then (if i.val < 1166 then (if i.val < 1165 then 71 else 81) else (if i.val < 1167 then 78 else (if i.val < 1168 then 59 else 78))) else (if i.val < 1171 then (if i.val < 1170 then 38 else 30) else (if i.val < 1172 then 45 else (if i.val < 1173 then 40 else 32)))))) else (if i.val < 1194 then (if i.val < 1184 then (if i.val < 1179 then (if i.val < 1176 then (if i.val < 1175 then 81 else 50) else (if i.val < 1177 then 34 else (if i.val < 1178 then 21 else 74))) else (if i.val < 1181 then (if i.val < 1180 then 86 else 50) else (if i.val < 1182 then 86 else (if i.val < 1183 then 8 else 40)))) else (if i.val < 1189 then (if i.val < 1186 then (if i.val < 1185 then 40 else 32) else (if i.val < 1187 then 93 else (if i.val < 1188 then 78 else 32))) else (if i.val < 1191 then (if i.val < 1190 then 51 else 85) else (if i.val < 1192 then 10 else (if i.val < 1193 then 21 else 25))))) else (if i.val < 1204 then (if i.val < 1199 then (if i.val < 1196 then (if i.val < 1195 then 40 else 21) else (if i.val < 1197 then 89 else (if i.val < 1198 then 57 else 46))) else (if i.val < 1201 then (if i.val < 1200 then 38 else 69) else (if i.val < 1202 then 38 else (if i.val < 1203 then 49 else 57)))) else (if i.val < 1209 then (if i.val < 1206 then (if i.val < 1205 then 46 else 34) else (if i.val < 1207 then 46 else (if i.val < 1208 then 34 else 13))) else (if i.val < 1212 then (if i.val < 1210 then 30 else (if i.val < 1211 then 21 else 50)) else (if i.val < 1213 then 13 else (if i.val < 1214 then 21 else 21))))))) else (if i.val < 1255 then (if i.val < 1235 then (if i.val < 1225 then (if i.val < 1220 then (if i.val < 1217 then (if i.val < 1216 then 49 else 57) else (if i.val < 1218 then 38 else (if i.val < 1219 then 57 else 38))) else (if i.val < 1222 then (if i.val < 1221 then 38 else 38) else (if i.val < 1223 then 49 else (if i.val < 1224 then 49 else 8)))) else (if i.val < 1230 then (if i.val < 1227 then (if i.val < 1226 then 49 else 69) else (if i.val < 1228 then 46 else (if i.val < 1229 then 34 else 13))) else (if i.val < 1232 then (if i.val < 1231 then 74 else 38) else (if i.val < 1233 then 38 else (if i.val < 1234 then 38 else 38))))) else (if i.val < 1245 then (if i.val < 1240 then (if i.val < 1237 then (if i.val < 1236 then 46 else 57) else (if i.val < 1238 then 57 else (if i.val < 1239 then 38 else 30))) else (if i.val < 1242 then (if i.val < 1241 then 64 else 38) else (if i.val < 1243 then 38 else (if i.val < 1244 then 57 else 15)))) else (if i.val < 1250 then (if i.val < 1247 then (if i.val < 1246 then 30 else 21) else (if i.val < 1248 then 89 else (if i.val < 1249 then 43 else 25))) else (if i.val < 1252 then (if i.val < 1251 then 30 else 29) else (if i.val < 1253 then 49 else (if i.val < 1254 then 51 else 85)))))) else (if i.val < 1275 then (if i.val < 1265 then (if i.val < 1260 then (if i.val < 1257 then (if i.val < 1256 then 59 else 69) else (if i.val < 1258 then 38 else (if i.val < 1259 then 38 else 30))) else (if i.val < 1262 then (if i.val < 1261 then 71 else 40) else (if i.val < 1263 then 21 else (if i.val < 1264 then 57 else 57)))) else (if i.val < 1270 then (if i.val < 1267 then (if i.val < 1266 then 38 else 75) else (if i.val < 1268 then 57 else (if i.val < 1269 then 69 else 11))) else (if i.val < 1272 then (if i.val < 1271 then 66 else 6) else (if i.val < 1273 then 56 else (if i.val < 1274 then 91 else 49))))) else (if i.val < 1285 then (if i.val < 1280 then (if i.val < 1277 then (if i.val < 1276 then 15 else 75) else (if i.val < 1278 then 11 else (if i.val < 1279 then 95 else 11))) else (if i.val < 1282 then (if i.val < 1281 then 44 else 6) else (if i.val < 1283 then 75 else (if i.val < 1284 then 56 else 69)))) else (if i.val < 1290 then (if i.val < 1287 then (if i.val < 1286 then 44 else 95) else (if i.val < 1288 then 4 else (if i.val < 1289 then 4 else 44))) else (if i.val < 1293 then (if i.val < 1291 then 95 else (if i.val < 1292 then 11 else 95)) else (if i.val < 1294 then 4 else (if i.val < 1295 then 4 else 38)))))))))))

def g32p_supplierGroup12_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 4, 6, 8, 10, 11, 13, 15, 18, 19, 21, 23, 24, 25, 28, 29, 30, 32, 34, 35, 37, 38, 40, 43, 44, 45, 46, 49, 50, 51, 56, 57, 59, 64, 65, 66, 67, 69, 71, 74, 75, 76, 77, 78, 79, 81, 82, 84, 85, 86, 87, 88, 89, 91, 92, 93, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup12_matrix_000 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 0 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 0 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 0 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 0 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 0 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_001 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 1 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 1 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 1 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 1 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 1 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_002 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 2 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 2 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 2 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 2 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 2 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_003 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 3 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 3 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 3 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 3 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 3 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_004 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 4 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 4 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 4 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 4 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 4 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_005 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 5 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 5 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 5 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 5 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 5 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_006 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 6 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 6 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 6 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 6 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 6 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_007 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 7 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 7 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 7 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 7 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 7 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_008 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 8 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 8 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 8 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 8 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 8 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_009 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 9 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 9 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 9 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 9 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 9 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_010 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 10 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 10 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 10 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 10 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 10 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_011 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 11 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 11 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 11 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 11 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 11 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_012 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 12 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 12 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 12 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 12 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 12 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_013 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 13 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 13 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 13 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 13 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 13 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_014 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 14 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 14 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 14 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 14 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 14 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_015 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 15 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 15 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 15 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 15 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 15 r) ∈ g32p_supplierGroup12_support := by
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

theorem g32p_supplierGroup12_matrix_016 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 16 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 16 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 16 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 16 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 16 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_017 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 17 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 17 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 17 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 17 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 17 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_018 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 18 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 18 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 18 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 18 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 18 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_019 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 19 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 19 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 19 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 19 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 19 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_020 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 20 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 20 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 20 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 20 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 20 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_021 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 21 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 21 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 21 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 21 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 21 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_022 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 22 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 22 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 22 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 22 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 22 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_023 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 23 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 23 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 23 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 23 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 23 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_024 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 24 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 24 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 24 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 24 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 24 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_025 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 25 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 25 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 25 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 25 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 25 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_026 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 26 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 26 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 26 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 26 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 26 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_027 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 27 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 27 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 27 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_027 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 27 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 27 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 27 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_027 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 27 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_028 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 28 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 28 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 28 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_028 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 28 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 28 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 28 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_028 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 28 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_029 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 29 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 29 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 29 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_029 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 29 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 29 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 29 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_029 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 29 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_030 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 30 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 30 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 30 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_030 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 30 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 30 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 30 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_030 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 30 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_031 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 31 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 31 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 31 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_031 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 31 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 31 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 31 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_031 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 31 r) ∈ g32p_supplierGroup12_support := by
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

theorem g32p_supplierGroup12_matrix_032 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 32 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 32 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 32 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_032 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 32 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 32 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 32 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_032 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 32 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_033 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 33 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 33 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 33 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_033 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 33 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 33 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 33 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_033 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 33 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_034 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 34 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 34 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 34 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_034 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 34 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 34 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 34 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_034 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 34 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_035 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 35 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 35 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 35 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_035 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 35 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 35 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 35 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_035 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 35 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_036 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 36 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 36 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 36 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_036 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 36 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 36 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 36 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_036 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 36 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_037 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 37 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 37 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 37 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_037 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 37 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 37 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 37 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_037 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 37 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_038 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 38 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 38 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 38 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_038 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 38 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 38 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 38 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_038 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 38 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_039 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 39 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 39 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 39 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_039 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 39 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 39 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 39 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_039 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 39 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_040 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 40 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 40 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 40 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_040 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 40 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 40 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 40 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_040 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 40 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_041 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 41 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 41 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 41 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_041 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 41 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 41 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 41 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_041 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 41 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_042 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 42 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 42 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 42 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_042 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 42 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 42 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 42 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_042 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 42 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_043 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 43 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 43 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 43 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_043 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 43 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 43 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 43 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_043 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 43 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_044 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 44 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 44 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 44 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_044 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 44 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 44 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 44 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_044 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 44 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_045 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 45 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 45 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 45 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_045 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 45 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 45 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 45 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_045 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 45 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_046 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 46 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 46 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 46 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_046 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 46 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 46 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 46 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_046 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 46 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_047 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 47 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 47 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 47 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_047 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 47 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 47 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 47 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_047 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 47 r) ∈ g32p_supplierGroup12_support := by
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

theorem g32p_supplierGroup12_matrix_048 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 48 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 48 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 48 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_048 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 48 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 48 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 48 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_048 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 48 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_049 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 49 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 49 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 49 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_049 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 49 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 49 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 49 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_049 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 49 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_050 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 50 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 50 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 50 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_050 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 50 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 50 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 50 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_050 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 50 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_051 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 51 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 51 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 51 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_051 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 51 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 51 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 51 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_051 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 51 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_052 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 52 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 52 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 52 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_052 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 52 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 52 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 52 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_052 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 52 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_053 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 53 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 53 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 53 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_053 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 53 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 53 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 53 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_053 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 53 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_054 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 54 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 54 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 54 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_054 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 54 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 54 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 54 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_054 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 54 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_055 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 55 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 55 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 55 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_055 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 55 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 55 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 55 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_055 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 55 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_056 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 56 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 56 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 56 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_056 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 56 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 56 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 56 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_056 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 56 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_057 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 57 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 57 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 57 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_057 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 57 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 57 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 57 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_057 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 57 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_058 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 58 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 58 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 58 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_058 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 58 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 58 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 58 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_058 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 58 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_059 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 59 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 59 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 59 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_059 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 59 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 59 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 59 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_059 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 59 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_060 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 60 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 60 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 60 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_060 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 60 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 60 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 60 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_060 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 60 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_061 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 61 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 61 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 61 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_061 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 61 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 61 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 61 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_061 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 61 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_062 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 62 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 62 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 62 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_062 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 62 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 62 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 62 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_062 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 62 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_063 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 63 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 63 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 63 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_063 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 63 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 63 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 63 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_063 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 63 r) ∈ g32p_supplierGroup12_support := by
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

theorem g32p_supplierGroup12_matrix_064 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 64 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 64 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 64 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_064 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 64 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 64 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 64 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_064 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 64 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_065 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 65 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 65 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 65 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_065 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 65 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 65 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 65 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_065 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 65 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_066 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 66 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 66 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 66 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_066 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 66 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 66 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 66 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_066 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 66 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_067 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 67 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 67 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 67 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_067 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 67 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 67 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 67 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_067 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 67 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_068 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 68 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 68 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 68 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_068 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 68 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 68 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 68 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_068 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 68 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_069 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 69 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 69 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 69 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_069 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 69 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 69 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 69 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_069 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 69 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_070 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 70 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 70 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 70 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_070 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 70 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 70 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 70 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_070 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 70 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_071 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 71 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 71 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 71 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_071 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 71 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 71 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 71 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_071 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 71 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_072 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 72 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 72 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 72 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_072 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 72 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 72 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 72 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_072 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 72 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_073 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 73 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 73 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 73 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_073 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 73 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 73 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 73 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_073 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 73 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_074 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 74 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 74 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 74 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_074 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 74 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 74 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 74 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_074 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 74 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_075 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 75 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 75 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 75 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_075 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 75 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 75 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 75 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_075 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 75 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_076 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 76 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 76 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 76 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_076 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 76 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 76 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 76 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_076 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 76 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_077 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 77 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 77 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 77 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_077 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 77 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 77 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 77 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_077 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 77 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_078 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 78 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 78 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 78 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_078 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 78 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 78 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 78 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_078 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 78 r) ∈ g32p_supplierGroup12_support := by
  decide +kernel

theorem g32p_supplierGroup12_matrix_079 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 79 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 79 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 79 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_079 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 79 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 79 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 79 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_079 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 79 r) ∈ g32p_supplierGroup12_support := by
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

theorem g32p_supplierGroup12_matrix_080 : ∀ r : Fin 16,
    g32p_row17_groupNodes (g32p_finBlockIndex 1296 80 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 80 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 80 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup12_class_080 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 80 r)).1 (g32p_supplierGroup12_source (g32p_finBlockIndex 1296 80 r)).2 =
      g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 80 r) := by
  decide +kernel

theorem g32p_supplierGroup12_support_080 : ∀ r : Fin 16,
    g32p_supplierGroup12_classify (g32p_finBlockIndex 1296 80 r) ∈ g32p_supplierGroup12_support := by
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

theorem g32p_supplierGroup12_matrix (i : Fin 1296) :
    g32p_row17_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source i).1 (g32p_supplierGroup12_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row17_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup12_source i).1 (g32p_supplierGroup12_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup12_matrix_000 r
  · exact g32p_supplierGroup12_matrix_001 r
  · exact g32p_supplierGroup12_matrix_002 r
  · exact g32p_supplierGroup12_matrix_003 r
  · exact g32p_supplierGroup12_matrix_004 r
  · exact g32p_supplierGroup12_matrix_005 r
  · exact g32p_supplierGroup12_matrix_006 r
  · exact g32p_supplierGroup12_matrix_007 r
  · exact g32p_supplierGroup12_matrix_008 r
  · exact g32p_supplierGroup12_matrix_009 r
  · exact g32p_supplierGroup12_matrix_010 r
  · exact g32p_supplierGroup12_matrix_011 r
  · exact g32p_supplierGroup12_matrix_012 r
  · exact g32p_supplierGroup12_matrix_013 r
  · exact g32p_supplierGroup12_matrix_014 r
  · exact g32p_supplierGroup12_matrix_015 r
  · exact g32p_supplierGroup12_matrix_016 r
  · exact g32p_supplierGroup12_matrix_017 r
  · exact g32p_supplierGroup12_matrix_018 r
  · exact g32p_supplierGroup12_matrix_019 r
  · exact g32p_supplierGroup12_matrix_020 r
  · exact g32p_supplierGroup12_matrix_021 r
  · exact g32p_supplierGroup12_matrix_022 r
  · exact g32p_supplierGroup12_matrix_023 r
  · exact g32p_supplierGroup12_matrix_024 r
  · exact g32p_supplierGroup12_matrix_025 r
  · exact g32p_supplierGroup12_matrix_026 r
  · exact g32p_supplierGroup12_matrix_027 r
  · exact g32p_supplierGroup12_matrix_028 r
  · exact g32p_supplierGroup12_matrix_029 r
  · exact g32p_supplierGroup12_matrix_030 r
  · exact g32p_supplierGroup12_matrix_031 r
  · exact g32p_supplierGroup12_matrix_032 r
  · exact g32p_supplierGroup12_matrix_033 r
  · exact g32p_supplierGroup12_matrix_034 r
  · exact g32p_supplierGroup12_matrix_035 r
  · exact g32p_supplierGroup12_matrix_036 r
  · exact g32p_supplierGroup12_matrix_037 r
  · exact g32p_supplierGroup12_matrix_038 r
  · exact g32p_supplierGroup12_matrix_039 r
  · exact g32p_supplierGroup12_matrix_040 r
  · exact g32p_supplierGroup12_matrix_041 r
  · exact g32p_supplierGroup12_matrix_042 r
  · exact g32p_supplierGroup12_matrix_043 r
  · exact g32p_supplierGroup12_matrix_044 r
  · exact g32p_supplierGroup12_matrix_045 r
  · exact g32p_supplierGroup12_matrix_046 r
  · exact g32p_supplierGroup12_matrix_047 r
  · exact g32p_supplierGroup12_matrix_048 r
  · exact g32p_supplierGroup12_matrix_049 r
  · exact g32p_supplierGroup12_matrix_050 r
  · exact g32p_supplierGroup12_matrix_051 r
  · exact g32p_supplierGroup12_matrix_052 r
  · exact g32p_supplierGroup12_matrix_053 r
  · exact g32p_supplierGroup12_matrix_054 r
  · exact g32p_supplierGroup12_matrix_055 r
  · exact g32p_supplierGroup12_matrix_056 r
  · exact g32p_supplierGroup12_matrix_057 r
  · exact g32p_supplierGroup12_matrix_058 r
  · exact g32p_supplierGroup12_matrix_059 r
  · exact g32p_supplierGroup12_matrix_060 r
  · exact g32p_supplierGroup12_matrix_061 r
  · exact g32p_supplierGroup12_matrix_062 r
  · exact g32p_supplierGroup12_matrix_063 r
  · exact g32p_supplierGroup12_matrix_064 r
  · exact g32p_supplierGroup12_matrix_065 r
  · exact g32p_supplierGroup12_matrix_066 r
  · exact g32p_supplierGroup12_matrix_067 r
  · exact g32p_supplierGroup12_matrix_068 r
  · exact g32p_supplierGroup12_matrix_069 r
  · exact g32p_supplierGroup12_matrix_070 r
  · exact g32p_supplierGroup12_matrix_071 r
  · exact g32p_supplierGroup12_matrix_072 r
  · exact g32p_supplierGroup12_matrix_073 r
  · exact g32p_supplierGroup12_matrix_074 r
  · exact g32p_supplierGroup12_matrix_075 r
  · exact g32p_supplierGroup12_matrix_076 r
  · exact g32p_supplierGroup12_matrix_077 r
  · exact g32p_supplierGroup12_matrix_078 r
  · exact g32p_supplierGroup12_matrix_079 r
  · exact g32p_supplierGroup12_matrix_080 r

theorem g32p_supplierGroup12_class (i : Fin 1296) :
    g32p_supplierForest_classes (g32p_supplierGroup12_source i).1 (g32p_supplierGroup12_source i).2 =
      g32p_supplierGroup12_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup12_source i).1 (g32p_supplierGroup12_source i).2 =
      g32p_supplierGroup12_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup12_class_000 r
  · exact g32p_supplierGroup12_class_001 r
  · exact g32p_supplierGroup12_class_002 r
  · exact g32p_supplierGroup12_class_003 r
  · exact g32p_supplierGroup12_class_004 r
  · exact g32p_supplierGroup12_class_005 r
  · exact g32p_supplierGroup12_class_006 r
  · exact g32p_supplierGroup12_class_007 r
  · exact g32p_supplierGroup12_class_008 r
  · exact g32p_supplierGroup12_class_009 r
  · exact g32p_supplierGroup12_class_010 r
  · exact g32p_supplierGroup12_class_011 r
  · exact g32p_supplierGroup12_class_012 r
  · exact g32p_supplierGroup12_class_013 r
  · exact g32p_supplierGroup12_class_014 r
  · exact g32p_supplierGroup12_class_015 r
  · exact g32p_supplierGroup12_class_016 r
  · exact g32p_supplierGroup12_class_017 r
  · exact g32p_supplierGroup12_class_018 r
  · exact g32p_supplierGroup12_class_019 r
  · exact g32p_supplierGroup12_class_020 r
  · exact g32p_supplierGroup12_class_021 r
  · exact g32p_supplierGroup12_class_022 r
  · exact g32p_supplierGroup12_class_023 r
  · exact g32p_supplierGroup12_class_024 r
  · exact g32p_supplierGroup12_class_025 r
  · exact g32p_supplierGroup12_class_026 r
  · exact g32p_supplierGroup12_class_027 r
  · exact g32p_supplierGroup12_class_028 r
  · exact g32p_supplierGroup12_class_029 r
  · exact g32p_supplierGroup12_class_030 r
  · exact g32p_supplierGroup12_class_031 r
  · exact g32p_supplierGroup12_class_032 r
  · exact g32p_supplierGroup12_class_033 r
  · exact g32p_supplierGroup12_class_034 r
  · exact g32p_supplierGroup12_class_035 r
  · exact g32p_supplierGroup12_class_036 r
  · exact g32p_supplierGroup12_class_037 r
  · exact g32p_supplierGroup12_class_038 r
  · exact g32p_supplierGroup12_class_039 r
  · exact g32p_supplierGroup12_class_040 r
  · exact g32p_supplierGroup12_class_041 r
  · exact g32p_supplierGroup12_class_042 r
  · exact g32p_supplierGroup12_class_043 r
  · exact g32p_supplierGroup12_class_044 r
  · exact g32p_supplierGroup12_class_045 r
  · exact g32p_supplierGroup12_class_046 r
  · exact g32p_supplierGroup12_class_047 r
  · exact g32p_supplierGroup12_class_048 r
  · exact g32p_supplierGroup12_class_049 r
  · exact g32p_supplierGroup12_class_050 r
  · exact g32p_supplierGroup12_class_051 r
  · exact g32p_supplierGroup12_class_052 r
  · exact g32p_supplierGroup12_class_053 r
  · exact g32p_supplierGroup12_class_054 r
  · exact g32p_supplierGroup12_class_055 r
  · exact g32p_supplierGroup12_class_056 r
  · exact g32p_supplierGroup12_class_057 r
  · exact g32p_supplierGroup12_class_058 r
  · exact g32p_supplierGroup12_class_059 r
  · exact g32p_supplierGroup12_class_060 r
  · exact g32p_supplierGroup12_class_061 r
  · exact g32p_supplierGroup12_class_062 r
  · exact g32p_supplierGroup12_class_063 r
  · exact g32p_supplierGroup12_class_064 r
  · exact g32p_supplierGroup12_class_065 r
  · exact g32p_supplierGroup12_class_066 r
  · exact g32p_supplierGroup12_class_067 r
  · exact g32p_supplierGroup12_class_068 r
  · exact g32p_supplierGroup12_class_069 r
  · exact g32p_supplierGroup12_class_070 r
  · exact g32p_supplierGroup12_class_071 r
  · exact g32p_supplierGroup12_class_072 r
  · exact g32p_supplierGroup12_class_073 r
  · exact g32p_supplierGroup12_class_074 r
  · exact g32p_supplierGroup12_class_075 r
  · exact g32p_supplierGroup12_class_076 r
  · exact g32p_supplierGroup12_class_077 r
  · exact g32p_supplierGroup12_class_078 r
  · exact g32p_supplierGroup12_class_079 r
  · exact g32p_supplierGroup12_class_080 r

theorem g32p_supplierGroup12_support_mem (i : Fin 1296) :
    g32p_supplierGroup12_classify i ∈ g32p_supplierGroup12_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup12_classify i ∈ g32p_supplierGroup12_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup12_support_000 r
  · exact g32p_supplierGroup12_support_001 r
  · exact g32p_supplierGroup12_support_002 r
  · exact g32p_supplierGroup12_support_003 r
  · exact g32p_supplierGroup12_support_004 r
  · exact g32p_supplierGroup12_support_005 r
  · exact g32p_supplierGroup12_support_006 r
  · exact g32p_supplierGroup12_support_007 r
  · exact g32p_supplierGroup12_support_008 r
  · exact g32p_supplierGroup12_support_009 r
  · exact g32p_supplierGroup12_support_010 r
  · exact g32p_supplierGroup12_support_011 r
  · exact g32p_supplierGroup12_support_012 r
  · exact g32p_supplierGroup12_support_013 r
  · exact g32p_supplierGroup12_support_014 r
  · exact g32p_supplierGroup12_support_015 r
  · exact g32p_supplierGroup12_support_016 r
  · exact g32p_supplierGroup12_support_017 r
  · exact g32p_supplierGroup12_support_018 r
  · exact g32p_supplierGroup12_support_019 r
  · exact g32p_supplierGroup12_support_020 r
  · exact g32p_supplierGroup12_support_021 r
  · exact g32p_supplierGroup12_support_022 r
  · exact g32p_supplierGroup12_support_023 r
  · exact g32p_supplierGroup12_support_024 r
  · exact g32p_supplierGroup12_support_025 r
  · exact g32p_supplierGroup12_support_026 r
  · exact g32p_supplierGroup12_support_027 r
  · exact g32p_supplierGroup12_support_028 r
  · exact g32p_supplierGroup12_support_029 r
  · exact g32p_supplierGroup12_support_030 r
  · exact g32p_supplierGroup12_support_031 r
  · exact g32p_supplierGroup12_support_032 r
  · exact g32p_supplierGroup12_support_033 r
  · exact g32p_supplierGroup12_support_034 r
  · exact g32p_supplierGroup12_support_035 r
  · exact g32p_supplierGroup12_support_036 r
  · exact g32p_supplierGroup12_support_037 r
  · exact g32p_supplierGroup12_support_038 r
  · exact g32p_supplierGroup12_support_039 r
  · exact g32p_supplierGroup12_support_040 r
  · exact g32p_supplierGroup12_support_041 r
  · exact g32p_supplierGroup12_support_042 r
  · exact g32p_supplierGroup12_support_043 r
  · exact g32p_supplierGroup12_support_044 r
  · exact g32p_supplierGroup12_support_045 r
  · exact g32p_supplierGroup12_support_046 r
  · exact g32p_supplierGroup12_support_047 r
  · exact g32p_supplierGroup12_support_048 r
  · exact g32p_supplierGroup12_support_049 r
  · exact g32p_supplierGroup12_support_050 r
  · exact g32p_supplierGroup12_support_051 r
  · exact g32p_supplierGroup12_support_052 r
  · exact g32p_supplierGroup12_support_053 r
  · exact g32p_supplierGroup12_support_054 r
  · exact g32p_supplierGroup12_support_055 r
  · exact g32p_supplierGroup12_support_056 r
  · exact g32p_supplierGroup12_support_057 r
  · exact g32p_supplierGroup12_support_058 r
  · exact g32p_supplierGroup12_support_059 r
  · exact g32p_supplierGroup12_support_060 r
  · exact g32p_supplierGroup12_support_061 r
  · exact g32p_supplierGroup12_support_062 r
  · exact g32p_supplierGroup12_support_063 r
  · exact g32p_supplierGroup12_support_064 r
  · exact g32p_supplierGroup12_support_065 r
  · exact g32p_supplierGroup12_support_066 r
  · exact g32p_supplierGroup12_support_067 r
  · exact g32p_supplierGroup12_support_068 r
  · exact g32p_supplierGroup12_support_069 r
  · exact g32p_supplierGroup12_support_070 r
  · exact g32p_supplierGroup12_support_071 r
  · exact g32p_supplierGroup12_support_072 r
  · exact g32p_supplierGroup12_support_073 r
  · exact g32p_supplierGroup12_support_074 r
  · exact g32p_supplierGroup12_support_075 r
  · exact g32p_supplierGroup12_support_076 r
  · exact g32p_supplierGroup12_support_077 r
  · exact g32p_supplierGroup12_support_078 r
  · exact g32p_supplierGroup12_support_079 r
  · exact g32p_supplierGroup12_support_080 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row17_supplierClassifier : Fin 1296 → Fin 102 := g32p_supplierGroup12_classify

theorem g32p_row17_groupEquiv_isConj (i : Fin 1296) :
    IsConj (g32p_row17_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row17_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup12_source i).1 (g32p_supplierGroup12_source i).2
  rw [g32p_supplierGroup12_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row17_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup12_matrix i)

def g32p_row17_supplierClass (h : (g32p_recordedSuppliers 16).H) : Fin 102 :=
  g32p_row17_supplierClassifier (g32p_row17_groupEquiv.symm h)

theorem g32p_row17_supplierClass_isConj (h : (g32p_recordedSuppliers 16).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row17_supplierClass h)) := by
  have he : (g32p_row17_groupEquiv (g32p_row17_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 16).H => (a : g32p_G))
      (g32p_row17_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row17_supplierClassifier (g32p_row17_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row17_groupEquiv_isConj (g32p_row17_groupEquiv.symm h)

theorem g32p_row17_supplierClass_iff (h : (g32p_recordedSuppliers 16).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row17_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row17_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row17_supplierClass_isConj h).symm

theorem g32p_row17_supplierClass_mem_support (h : (g32p_recordedSuppliers 16).H) :
    g32p_row17_supplierClass h ∈ g32p_supplierGroup12_support :=
  g32p_supplierGroup12_support_mem (g32p_row17_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_000 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 0 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_000_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 0 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 0 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 0 10 10, g32p_row17_traceSegment_000_0000_0010, g32p_row17_traceSegment_000_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 20 10 10, g32p_row17_traceSegment_000_0020_0010, g32p_row17_traceSegment_000_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 0 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 0 20 20, g32p_row17_traceSegment_000_0000_0020, g32p_row17_traceSegment_000_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 40 10 10, g32p_row17_traceSegment_000_0040_0010, g32p_row17_traceSegment_000_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 60 10 11, g32p_row17_traceSegment_000_0060_0010, g32p_row17_traceSegment_000_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 40 20 21, g32p_row17_traceSegment_000_0040_0020, g32p_row17_traceSegment_000_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 0 40 41, g32p_row17_traceSegment_000_0000_0040, g32p_row17_traceSegment_000_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 81 10 10, g32p_row17_traceSegment_000_0081_0010, g32p_row17_traceSegment_000_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 101 10 10, g32p_row17_traceSegment_000_0101_0010, g32p_row17_traceSegment_000_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 81 20 20, g32p_row17_traceSegment_000_0081_0020, g32p_row17_traceSegment_000_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 121 10 10, g32p_row17_traceSegment_000_0121_0010, g32p_row17_traceSegment_000_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 141 10 11, g32p_row17_traceSegment_000_0141_0010, g32p_row17_traceSegment_000_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 121 20 21, g32p_row17_traceSegment_000_0121_0020, g32p_row17_traceSegment_000_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 81 40 41, g32p_row17_traceSegment_000_0081_0040, g32p_row17_traceSegment_000_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_000 0 162 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 0 81 81, g32p_row17_traceSegment_000_0000_0081, g32p_row17_traceSegment_000_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 162 10 10, g32p_row17_traceSegment_000_0162_0010, g32p_row17_traceSegment_000_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 182 10 10, g32p_row17_traceSegment_000_0182_0010, g32p_row17_traceSegment_000_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 162 20 20, g32p_row17_traceSegment_000_0162_0020, g32p_row17_traceSegment_000_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 202 10 10, g32p_row17_traceSegment_000_0202_0010, g32p_row17_traceSegment_000_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 222 10 11, g32p_row17_traceSegment_000_0222_0010, g32p_row17_traceSegment_000_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 202 20 21, g32p_row17_traceSegment_000_0202_0020, g32p_row17_traceSegment_000_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 162 40 41, g32p_row17_traceSegment_000_0162_0040, g32p_row17_traceSegment_000_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 243 10 10, g32p_row17_traceSegment_000_0243_0010, g32p_row17_traceSegment_000_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 263 10 10, g32p_row17_traceSegment_000_0263_0010, g32p_row17_traceSegment_000_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 243 20 20, g32p_row17_traceSegment_000_0243_0020, g32p_row17_traceSegment_000_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 283 10 10, g32p_row17_traceSegment_000_0283_0010, g32p_row17_traceSegment_000_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 303 10 11, g32p_row17_traceSegment_000_0303_0010, g32p_row17_traceSegment_000_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 283 20 21, g32p_row17_traceSegment_000_0283_0020, g32p_row17_traceSegment_000_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 243 40 41, g32p_row17_traceSegment_000_0243_0040, g32p_row17_traceSegment_000_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_000 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 162 81 81, g32p_row17_traceSegment_000_0162_0081, g32p_row17_traceSegment_000_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_000 0 324 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 0 162 162, g32p_row17_traceSegment_000_0000_0162, g32p_row17_traceSegment_000_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 324 10 10, g32p_row17_traceSegment_000_0324_0010, g32p_row17_traceSegment_000_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 344 10 10, g32p_row17_traceSegment_000_0344_0010, g32p_row17_traceSegment_000_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 324 20 20, g32p_row17_traceSegment_000_0324_0020, g32p_row17_traceSegment_000_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 364 10 10, g32p_row17_traceSegment_000_0364_0010, g32p_row17_traceSegment_000_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 384 10 11, g32p_row17_traceSegment_000_0384_0010, g32p_row17_traceSegment_000_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 364 20 21, g32p_row17_traceSegment_000_0364_0020, g32p_row17_traceSegment_000_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 324 40 41, g32p_row17_traceSegment_000_0324_0040, g32p_row17_traceSegment_000_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 405 10 10, g32p_row17_traceSegment_000_0405_0010, g32p_row17_traceSegment_000_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 425 10 10, g32p_row17_traceSegment_000_0425_0010, g32p_row17_traceSegment_000_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 405 20 20, g32p_row17_traceSegment_000_0405_0020, g32p_row17_traceSegment_000_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 445 10 10, g32p_row17_traceSegment_000_0445_0010, g32p_row17_traceSegment_000_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 465 10 11, g32p_row17_traceSegment_000_0465_0010, g32p_row17_traceSegment_000_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 445 20 21, g32p_row17_traceSegment_000_0445_0020, g32p_row17_traceSegment_000_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 405 40 41, g32p_row17_traceSegment_000_0405_0040, g32p_row17_traceSegment_000_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_000 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 324 81 81, g32p_row17_traceSegment_000_0324_0081, g32p_row17_traceSegment_000_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 486 10 10, g32p_row17_traceSegment_000_0486_0010, g32p_row17_traceSegment_000_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 506 10 10, g32p_row17_traceSegment_000_0506_0010, g32p_row17_traceSegment_000_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 486 20 20, g32p_row17_traceSegment_000_0486_0020, g32p_row17_traceSegment_000_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 526 10 10, g32p_row17_traceSegment_000_0526_0010, g32p_row17_traceSegment_000_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 546 10 11, g32p_row17_traceSegment_000_0546_0010, g32p_row17_traceSegment_000_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 526 20 21, g32p_row17_traceSegment_000_0526_0020, g32p_row17_traceSegment_000_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 486 40 41, g32p_row17_traceSegment_000_0486_0040, g32p_row17_traceSegment_000_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 567 10 10, g32p_row17_traceSegment_000_0567_0010, g32p_row17_traceSegment_000_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 587 10 10, g32p_row17_traceSegment_000_0587_0010, g32p_row17_traceSegment_000_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 567 20 20, g32p_row17_traceSegment_000_0567_0020, g32p_row17_traceSegment_000_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 607 10 10, g32p_row17_traceSegment_000_0607_0010, g32p_row17_traceSegment_000_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 627 10 11, g32p_row17_traceSegment_000_0627_0010, g32p_row17_traceSegment_000_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 607 20 21, g32p_row17_traceSegment_000_0607_0020, g32p_row17_traceSegment_000_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 567 40 41, g32p_row17_traceSegment_000_0567_0040, g32p_row17_traceSegment_000_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_000 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 486 81 81, g32p_row17_traceSegment_000_0486_0081, g32p_row17_traceSegment_000_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_000 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 324 162 162, g32p_row17_traceSegment_000_0324_0162, g32p_row17_traceSegment_000_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_000 0 648 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 0 324 324, g32p_row17_traceSegment_000_0000_0324, g32p_row17_traceSegment_000_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 648 10 10, g32p_row17_traceSegment_000_0648_0010, g32p_row17_traceSegment_000_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 668 10 10, g32p_row17_traceSegment_000_0668_0010, g32p_row17_traceSegment_000_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 648 20 20, g32p_row17_traceSegment_000_0648_0020, g32p_row17_traceSegment_000_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 688 10 10, g32p_row17_traceSegment_000_0688_0010, g32p_row17_traceSegment_000_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 708 10 11, g32p_row17_traceSegment_000_0708_0010, g32p_row17_traceSegment_000_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 688 20 21, g32p_row17_traceSegment_000_0688_0020, g32p_row17_traceSegment_000_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 648 40 41, g32p_row17_traceSegment_000_0648_0040, g32p_row17_traceSegment_000_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 729 10 10, g32p_row17_traceSegment_000_0729_0010, g32p_row17_traceSegment_000_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 749 10 10, g32p_row17_traceSegment_000_0749_0010, g32p_row17_traceSegment_000_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 729 20 20, g32p_row17_traceSegment_000_0729_0020, g32p_row17_traceSegment_000_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 769 10 10, g32p_row17_traceSegment_000_0769_0010, g32p_row17_traceSegment_000_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 789 10 11, g32p_row17_traceSegment_000_0789_0010, g32p_row17_traceSegment_000_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 769 20 21, g32p_row17_traceSegment_000_0769_0020, g32p_row17_traceSegment_000_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 729 40 41, g32p_row17_traceSegment_000_0729_0040, g32p_row17_traceSegment_000_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_000 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 648 81 81, g32p_row17_traceSegment_000_0648_0081, g32p_row17_traceSegment_000_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 810 10 10, g32p_row17_traceSegment_000_0810_0010, g32p_row17_traceSegment_000_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 830 10 10, g32p_row17_traceSegment_000_0830_0010, g32p_row17_traceSegment_000_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 810 20 20, g32p_row17_traceSegment_000_0810_0020, g32p_row17_traceSegment_000_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 850 10 10, g32p_row17_traceSegment_000_0850_0010, g32p_row17_traceSegment_000_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 870 10 11, g32p_row17_traceSegment_000_0870_0010, g32p_row17_traceSegment_000_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 850 20 21, g32p_row17_traceSegment_000_0850_0020, g32p_row17_traceSegment_000_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 810 40 41, g32p_row17_traceSegment_000_0810_0040, g32p_row17_traceSegment_000_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 891 10 10, g32p_row17_traceSegment_000_0891_0010, g32p_row17_traceSegment_000_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 911 10 10, g32p_row17_traceSegment_000_0911_0010, g32p_row17_traceSegment_000_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 891 20 20, g32p_row17_traceSegment_000_0891_0020, g32p_row17_traceSegment_000_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 931 10 10, g32p_row17_traceSegment_000_0931_0010, g32p_row17_traceSegment_000_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 951 10 11, g32p_row17_traceSegment_000_0951_0010, g32p_row17_traceSegment_000_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 931 20 21, g32p_row17_traceSegment_000_0931_0020, g32p_row17_traceSegment_000_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 891 40 41, g32p_row17_traceSegment_000_0891_0040, g32p_row17_traceSegment_000_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_000 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 810 81 81, g32p_row17_traceSegment_000_0810_0081, g32p_row17_traceSegment_000_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_000 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 648 162 162, g32p_row17_traceSegment_000_0648_0162, g32p_row17_traceSegment_000_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 972 10 10, g32p_row17_traceSegment_000_0972_0010, g32p_row17_traceSegment_000_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 992 10 10, g32p_row17_traceSegment_000_0992_0010, g32p_row17_traceSegment_000_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 972 20 20, g32p_row17_traceSegment_000_0972_0020, g32p_row17_traceSegment_000_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1012 10 10, g32p_row17_traceSegment_000_1012_0010, g32p_row17_traceSegment_000_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1032 10 11, g32p_row17_traceSegment_000_1032_0010, g32p_row17_traceSegment_000_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1012 20 21, g32p_row17_traceSegment_000_1012_0020, g32p_row17_traceSegment_000_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 972 40 41, g32p_row17_traceSegment_000_0972_0040, g32p_row17_traceSegment_000_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1053 10 10, g32p_row17_traceSegment_000_1053_0010, g32p_row17_traceSegment_000_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1073 10 10, g32p_row17_traceSegment_000_1073_0010, g32p_row17_traceSegment_000_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1053 20 20, g32p_row17_traceSegment_000_1053_0020, g32p_row17_traceSegment_000_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1093 10 10, g32p_row17_traceSegment_000_1093_0010, g32p_row17_traceSegment_000_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1113 10 11, g32p_row17_traceSegment_000_1113_0010, g32p_row17_traceSegment_000_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1093 20 21, g32p_row17_traceSegment_000_1093_0020, g32p_row17_traceSegment_000_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1053 40 41, g32p_row17_traceSegment_000_1053_0040, g32p_row17_traceSegment_000_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_000 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 972 81 81, g32p_row17_traceSegment_000_0972_0081, g32p_row17_traceSegment_000_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1134 10 10, g32p_row17_traceSegment_000_1134_0010, g32p_row17_traceSegment_000_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1154 10 10, g32p_row17_traceSegment_000_1154_0010, g32p_row17_traceSegment_000_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1134 20 20, g32p_row17_traceSegment_000_1134_0020, g32p_row17_traceSegment_000_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1174 10 10, g32p_row17_traceSegment_000_1174_0010, g32p_row17_traceSegment_000_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1194 10 11, g32p_row17_traceSegment_000_1194_0010, g32p_row17_traceSegment_000_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1174 20 21, g32p_row17_traceSegment_000_1174_0020, g32p_row17_traceSegment_000_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1134 40 41, g32p_row17_traceSegment_000_1134_0040, g32p_row17_traceSegment_000_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1215 10 10, g32p_row17_traceSegment_000_1215_0010, g32p_row17_traceSegment_000_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1235 10 10, g32p_row17_traceSegment_000_1235_0010, g32p_row17_traceSegment_000_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_000 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1215 20 20, g32p_row17_traceSegment_000_1215_0020, g32p_row17_traceSegment_000_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_000 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1255 10 10, g32p_row17_traceSegment_000_1255_0010, g32p_row17_traceSegment_000_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_000 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_000 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_000_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_000 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1275 10 11, g32p_row17_traceSegment_000_1275_0010, g32p_row17_traceSegment_000_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_000 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1255 20 21, g32p_row17_traceSegment_000_1255_0020, g32p_row17_traceSegment_000_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_000 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1215 40 41, g32p_row17_traceSegment_000_1215_0040, g32p_row17_traceSegment_000_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_000_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_000 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 1134 81 81, g32p_row17_traceSegment_000_1134_0081, g32p_row17_traceSegment_000_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_000 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 972 162 162, g32p_row17_traceSegment_000_0972_0162, g32p_row17_traceSegment_000_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_000 648 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 648 324 324, g32p_row17_traceSegment_000_0648_0324, g32p_row17_traceSegment_000_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_000_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_000 0 1296 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_000 0 648 648, g32p_row17_traceSegment_000_0000_0648, g32p_row17_traceSegment_000_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 0 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_000_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_001 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 1 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_001_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 0 10 10, g32p_row17_traceSegment_001_0000_0010, g32p_row17_traceSegment_001_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 20 10 10, g32p_row17_traceSegment_001_0020_0010, g32p_row17_traceSegment_001_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 0 20 20, g32p_row17_traceSegment_001_0000_0020, g32p_row17_traceSegment_001_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 40 10 10, g32p_row17_traceSegment_001_0040_0010, g32p_row17_traceSegment_001_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 60 10 11, g32p_row17_traceSegment_001_0060_0010, g32p_row17_traceSegment_001_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 40 20 21, g32p_row17_traceSegment_001_0040_0020, g32p_row17_traceSegment_001_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 0 40 41, g32p_row17_traceSegment_001_0000_0040, g32p_row17_traceSegment_001_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 81 10 10, g32p_row17_traceSegment_001_0081_0010, g32p_row17_traceSegment_001_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 101 10 10, g32p_row17_traceSegment_001_0101_0010, g32p_row17_traceSegment_001_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 81 20 20, g32p_row17_traceSegment_001_0081_0020, g32p_row17_traceSegment_001_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 121 10 10, g32p_row17_traceSegment_001_0121_0010, g32p_row17_traceSegment_001_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 141 10 11, g32p_row17_traceSegment_001_0141_0010, g32p_row17_traceSegment_001_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 121 20 21, g32p_row17_traceSegment_001_0121_0020, g32p_row17_traceSegment_001_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 81 40 41, g32p_row17_traceSegment_001_0081_0040, g32p_row17_traceSegment_001_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_001 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 0 81 81, g32p_row17_traceSegment_001_0000_0081, g32p_row17_traceSegment_001_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 162 10 10, g32p_row17_traceSegment_001_0162_0010, g32p_row17_traceSegment_001_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 182 10 10, g32p_row17_traceSegment_001_0182_0010, g32p_row17_traceSegment_001_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 162 20 20, g32p_row17_traceSegment_001_0162_0020, g32p_row17_traceSegment_001_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 202 10 10, g32p_row17_traceSegment_001_0202_0010, g32p_row17_traceSegment_001_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 222 10 11, g32p_row17_traceSegment_001_0222_0010, g32p_row17_traceSegment_001_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 202 20 21, g32p_row17_traceSegment_001_0202_0020, g32p_row17_traceSegment_001_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 162 40 41, g32p_row17_traceSegment_001_0162_0040, g32p_row17_traceSegment_001_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 243 10 10, g32p_row17_traceSegment_001_0243_0010, g32p_row17_traceSegment_001_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 263 10 10, g32p_row17_traceSegment_001_0263_0010, g32p_row17_traceSegment_001_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 243 20 20, g32p_row17_traceSegment_001_0243_0020, g32p_row17_traceSegment_001_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 283 10 10, g32p_row17_traceSegment_001_0283_0010, g32p_row17_traceSegment_001_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 303 10 11, g32p_row17_traceSegment_001_0303_0010, g32p_row17_traceSegment_001_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 283 20 21, g32p_row17_traceSegment_001_0283_0020, g32p_row17_traceSegment_001_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 243 40 41, g32p_row17_traceSegment_001_0243_0040, g32p_row17_traceSegment_001_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_001 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 162 81 81, g32p_row17_traceSegment_001_0162_0081, g32p_row17_traceSegment_001_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_001 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 0 162 162, g32p_row17_traceSegment_001_0000_0162, g32p_row17_traceSegment_001_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 324 10 10, g32p_row17_traceSegment_001_0324_0010, g32p_row17_traceSegment_001_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 344 10 10, g32p_row17_traceSegment_001_0344_0010, g32p_row17_traceSegment_001_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 324 20 20, g32p_row17_traceSegment_001_0324_0020, g32p_row17_traceSegment_001_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 364 10 10, g32p_row17_traceSegment_001_0364_0010, g32p_row17_traceSegment_001_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 384 10 11, g32p_row17_traceSegment_001_0384_0010, g32p_row17_traceSegment_001_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 364 20 21, g32p_row17_traceSegment_001_0364_0020, g32p_row17_traceSegment_001_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 324 40 41, g32p_row17_traceSegment_001_0324_0040, g32p_row17_traceSegment_001_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 405 10 10, g32p_row17_traceSegment_001_0405_0010, g32p_row17_traceSegment_001_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 425 10 10, g32p_row17_traceSegment_001_0425_0010, g32p_row17_traceSegment_001_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 405 20 20, g32p_row17_traceSegment_001_0405_0020, g32p_row17_traceSegment_001_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 445 10 10, g32p_row17_traceSegment_001_0445_0010, g32p_row17_traceSegment_001_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 465 10 11, g32p_row17_traceSegment_001_0465_0010, g32p_row17_traceSegment_001_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 445 20 21, g32p_row17_traceSegment_001_0445_0020, g32p_row17_traceSegment_001_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 405 40 41, g32p_row17_traceSegment_001_0405_0040, g32p_row17_traceSegment_001_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_001 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 324 81 81, g32p_row17_traceSegment_001_0324_0081, g32p_row17_traceSegment_001_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 486 10 10, g32p_row17_traceSegment_001_0486_0010, g32p_row17_traceSegment_001_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 506 10 10, g32p_row17_traceSegment_001_0506_0010, g32p_row17_traceSegment_001_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 486 20 20, g32p_row17_traceSegment_001_0486_0020, g32p_row17_traceSegment_001_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 526 10 10, g32p_row17_traceSegment_001_0526_0010, g32p_row17_traceSegment_001_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 546 10 11, g32p_row17_traceSegment_001_0546_0010, g32p_row17_traceSegment_001_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 526 20 21, g32p_row17_traceSegment_001_0526_0020, g32p_row17_traceSegment_001_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 486 40 41, g32p_row17_traceSegment_001_0486_0040, g32p_row17_traceSegment_001_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 577 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 567 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 567 10 10, g32p_row17_traceSegment_001_0567_0010, g32p_row17_traceSegment_001_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 597 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 587 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 587 10 10, g32p_row17_traceSegment_001_0587_0010, g32p_row17_traceSegment_001_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 567 40 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 567 20 20, g32p_row17_traceSegment_001_0567_0020, g32p_row17_traceSegment_001_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 607 10 10, g32p_row17_traceSegment_001_0607_0010, g32p_row17_traceSegment_001_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 627 10 11, g32p_row17_traceSegment_001_0627_0010, g32p_row17_traceSegment_001_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 607 20 21, g32p_row17_traceSegment_001_0607_0020, g32p_row17_traceSegment_001_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 567 81 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 567 40 41, g32p_row17_traceSegment_001_0567_0040, g32p_row17_traceSegment_001_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_001 486 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 486 81 81, g32p_row17_traceSegment_001_0486_0081, g32p_row17_traceSegment_001_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_001 324 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 324 162 162, g32p_row17_traceSegment_001_0324_0162, g32p_row17_traceSegment_001_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_001 0 648 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 0 324 324, g32p_row17_traceSegment_001_0000_0324, g32p_row17_traceSegment_001_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 648 10 10, g32p_row17_traceSegment_001_0648_0010, g32p_row17_traceSegment_001_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 678 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 668 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 668 10 10, g32p_row17_traceSegment_001_0668_0010, g32p_row17_traceSegment_001_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 648 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 648 20 20, g32p_row17_traceSegment_001_0648_0020, g32p_row17_traceSegment_001_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 688 10 10, g32p_row17_traceSegment_001_0688_0010, g32p_row17_traceSegment_001_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 708 10 11, g32p_row17_traceSegment_001_0708_0010, g32p_row17_traceSegment_001_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 688 20 21, g32p_row17_traceSegment_001_0688_0020, g32p_row17_traceSegment_001_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 648 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 648 40 41, g32p_row17_traceSegment_001_0648_0040, g32p_row17_traceSegment_001_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 739 10 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 729 20 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 729 10 10, g32p_row17_traceSegment_001_0729_0010, g32p_row17_traceSegment_001_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 749 10 10, g32p_row17_traceSegment_001_0749_0010, g32p_row17_traceSegment_001_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 729 40 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 729 20 20, g32p_row17_traceSegment_001_0729_0020, g32p_row17_traceSegment_001_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 769 10 10, g32p_row17_traceSegment_001_0769_0010, g32p_row17_traceSegment_001_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 789 10 11, g32p_row17_traceSegment_001_0789_0010, g32p_row17_traceSegment_001_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 769 20 21, g32p_row17_traceSegment_001_0769_0020, g32p_row17_traceSegment_001_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 729 81 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 729 40 41, g32p_row17_traceSegment_001_0729_0040, g32p_row17_traceSegment_001_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_001 648 162 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 648 81 81, g32p_row17_traceSegment_001_0648_0081, g32p_row17_traceSegment_001_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 810 10 10, g32p_row17_traceSegment_001_0810_0010, g32p_row17_traceSegment_001_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 830 10 10, g32p_row17_traceSegment_001_0830_0010, g32p_row17_traceSegment_001_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 810 20 20, g32p_row17_traceSegment_001_0810_0020, g32p_row17_traceSegment_001_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 850 10 10, g32p_row17_traceSegment_001_0850_0010, g32p_row17_traceSegment_001_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 870 10 11, g32p_row17_traceSegment_001_0870_0010, g32p_row17_traceSegment_001_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 850 20 21, g32p_row17_traceSegment_001_0850_0020, g32p_row17_traceSegment_001_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 810 40 41, g32p_row17_traceSegment_001_0810_0040, g32p_row17_traceSegment_001_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 891 10 10, g32p_row17_traceSegment_001_0891_0010, g32p_row17_traceSegment_001_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 911 10 10, g32p_row17_traceSegment_001_0911_0010, g32p_row17_traceSegment_001_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 891 20 20, g32p_row17_traceSegment_001_0891_0020, g32p_row17_traceSegment_001_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 931 10 10, g32p_row17_traceSegment_001_0931_0010, g32p_row17_traceSegment_001_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 951 10 11, g32p_row17_traceSegment_001_0951_0010, g32p_row17_traceSegment_001_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 931 20 21, g32p_row17_traceSegment_001_0931_0020, g32p_row17_traceSegment_001_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 891 40 41, g32p_row17_traceSegment_001_0891_0040, g32p_row17_traceSegment_001_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_001 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 810 81 81, g32p_row17_traceSegment_001_0810_0081, g32p_row17_traceSegment_001_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_001 648 324 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 648 162 162, g32p_row17_traceSegment_001_0648_0162, g32p_row17_traceSegment_001_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 972 10 10, g32p_row17_traceSegment_001_0972_0010, g32p_row17_traceSegment_001_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 992 10 10, g32p_row17_traceSegment_001_0992_0010, g32p_row17_traceSegment_001_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 972 20 20, g32p_row17_traceSegment_001_0972_0020, g32p_row17_traceSegment_001_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1012 10 10, g32p_row17_traceSegment_001_1012_0010, g32p_row17_traceSegment_001_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1032 10 11, g32p_row17_traceSegment_001_1032_0010, g32p_row17_traceSegment_001_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1012 20 21, g32p_row17_traceSegment_001_1012_0020, g32p_row17_traceSegment_001_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 972 40 41, g32p_row17_traceSegment_001_0972_0040, g32p_row17_traceSegment_001_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1053 10 10, g32p_row17_traceSegment_001_1053_0010, g32p_row17_traceSegment_001_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1073 10 10, g32p_row17_traceSegment_001_1073_0010, g32p_row17_traceSegment_001_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1053 20 20, g32p_row17_traceSegment_001_1053_0020, g32p_row17_traceSegment_001_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1093 10 10, g32p_row17_traceSegment_001_1093_0010, g32p_row17_traceSegment_001_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1113 10 11, g32p_row17_traceSegment_001_1113_0010, g32p_row17_traceSegment_001_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1093 20 21, g32p_row17_traceSegment_001_1093_0020, g32p_row17_traceSegment_001_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1053 40 41, g32p_row17_traceSegment_001_1053_0040, g32p_row17_traceSegment_001_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_001 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 972 81 81, g32p_row17_traceSegment_001_0972_0081, g32p_row17_traceSegment_001_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1134 10 10, g32p_row17_traceSegment_001_1134_0010, g32p_row17_traceSegment_001_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1154 10 10, g32p_row17_traceSegment_001_1154_0010, g32p_row17_traceSegment_001_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1134 20 20, g32p_row17_traceSegment_001_1134_0020, g32p_row17_traceSegment_001_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1174 10 10, g32p_row17_traceSegment_001_1174_0010, g32p_row17_traceSegment_001_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1194 10 11, g32p_row17_traceSegment_001_1194_0010, g32p_row17_traceSegment_001_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1174 20 21, g32p_row17_traceSegment_001_1174_0020, g32p_row17_traceSegment_001_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1134 40 41, g32p_row17_traceSegment_001_1134_0040, g32p_row17_traceSegment_001_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1215 10 10, g32p_row17_traceSegment_001_1215_0010, g32p_row17_traceSegment_001_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1235 10 10, g32p_row17_traceSegment_001_1235_0010, g32p_row17_traceSegment_001_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_001 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1215 20 20, g32p_row17_traceSegment_001_1215_0020, g32p_row17_traceSegment_001_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_001 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1255 10 10, g32p_row17_traceSegment_001_1255_0010, g32p_row17_traceSegment_001_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_001 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_001 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_001_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_001 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1275 10 11, g32p_row17_traceSegment_001_1275_0010, g32p_row17_traceSegment_001_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_001 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1255 20 21, g32p_row17_traceSegment_001_1255_0020, g32p_row17_traceSegment_001_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_001 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1215 40 41, g32p_row17_traceSegment_001_1215_0040, g32p_row17_traceSegment_001_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_001_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_001 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 1134 81 81, g32p_row17_traceSegment_001_1134_0081, g32p_row17_traceSegment_001_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_001 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 972 162 162, g32p_row17_traceSegment_001_0972_0162, g32p_row17_traceSegment_001_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_001 648 648 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 648 324 324, g32p_row17_traceSegment_001_0648_0324, g32p_row17_traceSegment_001_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_001_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_001 0 1296 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_001 0 648 648, g32p_row17_traceSegment_001_0000_0648, g32p_row17_traceSegment_001_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 1 = [0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_001_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_002 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 2 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_002_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 0 10 10, g32p_row17_traceSegment_002_0000_0010, g32p_row17_traceSegment_002_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 20 10 10, g32p_row17_traceSegment_002_0020_0010, g32p_row17_traceSegment_002_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 0 20 20, g32p_row17_traceSegment_002_0000_0020, g32p_row17_traceSegment_002_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 40 10 10, g32p_row17_traceSegment_002_0040_0010, g32p_row17_traceSegment_002_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 60 10 11, g32p_row17_traceSegment_002_0060_0010, g32p_row17_traceSegment_002_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 40 20 21, g32p_row17_traceSegment_002_0040_0020, g32p_row17_traceSegment_002_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 0 40 41, g32p_row17_traceSegment_002_0000_0040, g32p_row17_traceSegment_002_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 81 10 10, g32p_row17_traceSegment_002_0081_0010, g32p_row17_traceSegment_002_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 101 10 10, g32p_row17_traceSegment_002_0101_0010, g32p_row17_traceSegment_002_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 81 20 20, g32p_row17_traceSegment_002_0081_0020, g32p_row17_traceSegment_002_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 121 10 10, g32p_row17_traceSegment_002_0121_0010, g32p_row17_traceSegment_002_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 141 10 11, g32p_row17_traceSegment_002_0141_0010, g32p_row17_traceSegment_002_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 121 20 21, g32p_row17_traceSegment_002_0121_0020, g32p_row17_traceSegment_002_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 81 40 41, g32p_row17_traceSegment_002_0081_0040, g32p_row17_traceSegment_002_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_002 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 0 81 81, g32p_row17_traceSegment_002_0000_0081, g32p_row17_traceSegment_002_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 162 10 10, g32p_row17_traceSegment_002_0162_0010, g32p_row17_traceSegment_002_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 182 10 10, g32p_row17_traceSegment_002_0182_0010, g32p_row17_traceSegment_002_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 162 20 20, g32p_row17_traceSegment_002_0162_0020, g32p_row17_traceSegment_002_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 202 10 10, g32p_row17_traceSegment_002_0202_0010, g32p_row17_traceSegment_002_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 222 10 11, g32p_row17_traceSegment_002_0222_0010, g32p_row17_traceSegment_002_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 202 20 21, g32p_row17_traceSegment_002_0202_0020, g32p_row17_traceSegment_002_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 162 40 41, g32p_row17_traceSegment_002_0162_0040, g32p_row17_traceSegment_002_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 243 10 10, g32p_row17_traceSegment_002_0243_0010, g32p_row17_traceSegment_002_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 263 10 10, g32p_row17_traceSegment_002_0263_0010, g32p_row17_traceSegment_002_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 243 20 20, g32p_row17_traceSegment_002_0243_0020, g32p_row17_traceSegment_002_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 283 10 10, g32p_row17_traceSegment_002_0283_0010, g32p_row17_traceSegment_002_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 303 10 11, g32p_row17_traceSegment_002_0303_0010, g32p_row17_traceSegment_002_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 283 20 21, g32p_row17_traceSegment_002_0283_0020, g32p_row17_traceSegment_002_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 243 40 41, g32p_row17_traceSegment_002_0243_0040, g32p_row17_traceSegment_002_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_002 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 162 81 81, g32p_row17_traceSegment_002_0162_0081, g32p_row17_traceSegment_002_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_002 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 0 162 162, g32p_row17_traceSegment_002_0000_0162, g32p_row17_traceSegment_002_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 324 10 10, g32p_row17_traceSegment_002_0324_0010, g32p_row17_traceSegment_002_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 344 10 10, g32p_row17_traceSegment_002_0344_0010, g32p_row17_traceSegment_002_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 324 20 20, g32p_row17_traceSegment_002_0324_0020, g32p_row17_traceSegment_002_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 364 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 364 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 364 10 10, g32p_row17_traceSegment_002_0364_0010, g32p_row17_traceSegment_002_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 384 10 11, g32p_row17_traceSegment_002_0384_0010, g32p_row17_traceSegment_002_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 364 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 364 20 21, g32p_row17_traceSegment_002_0364_0020, g32p_row17_traceSegment_002_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 324 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 324 40 41, g32p_row17_traceSegment_002_0324_0040, g32p_row17_traceSegment_002_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 405 10 10, g32p_row17_traceSegment_002_0405_0010, g32p_row17_traceSegment_002_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 425 10 10, g32p_row17_traceSegment_002_0425_0010, g32p_row17_traceSegment_002_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 405 20 20, g32p_row17_traceSegment_002_0405_0020, g32p_row17_traceSegment_002_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 445 10 10, g32p_row17_traceSegment_002_0445_0010, g32p_row17_traceSegment_002_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 465 10 11, g32p_row17_traceSegment_002_0465_0010, g32p_row17_traceSegment_002_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 445 20 21, g32p_row17_traceSegment_002_0445_0020, g32p_row17_traceSegment_002_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 405 40 41, g32p_row17_traceSegment_002_0405_0040, g32p_row17_traceSegment_002_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_002 324 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 324 81 81, g32p_row17_traceSegment_002_0324_0081, g32p_row17_traceSegment_002_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 486 10 10, g32p_row17_traceSegment_002_0486_0010, g32p_row17_traceSegment_002_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 506 10 10, g32p_row17_traceSegment_002_0506_0010, g32p_row17_traceSegment_002_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 486 20 20, g32p_row17_traceSegment_002_0486_0020, g32p_row17_traceSegment_002_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 526 10 10, g32p_row17_traceSegment_002_0526_0010, g32p_row17_traceSegment_002_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 546 10 11, g32p_row17_traceSegment_002_0546_0010, g32p_row17_traceSegment_002_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 526 20 21, g32p_row17_traceSegment_002_0526_0020, g32p_row17_traceSegment_002_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 486 40 41, g32p_row17_traceSegment_002_0486_0040, g32p_row17_traceSegment_002_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 567 10 10, g32p_row17_traceSegment_002_0567_0010, g32p_row17_traceSegment_002_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 587 10 10, g32p_row17_traceSegment_002_0587_0010, g32p_row17_traceSegment_002_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 567 20 20, g32p_row17_traceSegment_002_0567_0020, g32p_row17_traceSegment_002_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 607 10 10, g32p_row17_traceSegment_002_0607_0010, g32p_row17_traceSegment_002_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 627 10 11, g32p_row17_traceSegment_002_0627_0010, g32p_row17_traceSegment_002_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 607 20 21, g32p_row17_traceSegment_002_0607_0020, g32p_row17_traceSegment_002_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 567 40 41, g32p_row17_traceSegment_002_0567_0040, g32p_row17_traceSegment_002_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_002 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 486 81 81, g32p_row17_traceSegment_002_0486_0081, g32p_row17_traceSegment_002_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_002 324 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 324 162 162, g32p_row17_traceSegment_002_0324_0162, g32p_row17_traceSegment_002_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_002 0 648 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 0 324 324, g32p_row17_traceSegment_002_0000_0324, g32p_row17_traceSegment_002_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 648 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 648 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 648 10 10, g32p_row17_traceSegment_002_0648_0010, g32p_row17_traceSegment_002_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 668 10 10, g32p_row17_traceSegment_002_0668_0010, g32p_row17_traceSegment_002_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 648 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 648 20 20, g32p_row17_traceSegment_002_0648_0020, g32p_row17_traceSegment_002_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 688 10 10, g32p_row17_traceSegment_002_0688_0010, g32p_row17_traceSegment_002_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 708 10 11, g32p_row17_traceSegment_002_0708_0010, g32p_row17_traceSegment_002_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 688 20 21, g32p_row17_traceSegment_002_0688_0020, g32p_row17_traceSegment_002_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 648 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 648 40 41, g32p_row17_traceSegment_002_0648_0040, g32p_row17_traceSegment_002_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 729 10 10, g32p_row17_traceSegment_002_0729_0010, g32p_row17_traceSegment_002_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 759 10 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 749 20 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 749 10 10, g32p_row17_traceSegment_002_0749_0010, g32p_row17_traceSegment_002_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 729 40 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 729 20 20, g32p_row17_traceSegment_002_0729_0020, g32p_row17_traceSegment_002_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 769 10 10, g32p_row17_traceSegment_002_0769_0010, g32p_row17_traceSegment_002_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 789 10 11, g32p_row17_traceSegment_002_0789_0010, g32p_row17_traceSegment_002_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 769 20 21, g32p_row17_traceSegment_002_0769_0020, g32p_row17_traceSegment_002_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 729 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 729 40 41, g32p_row17_traceSegment_002_0729_0040, g32p_row17_traceSegment_002_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_002 648 162 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 648 81 81, g32p_row17_traceSegment_002_0648_0081, g32p_row17_traceSegment_002_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 810 10 10, g32p_row17_traceSegment_002_0810_0010, g32p_row17_traceSegment_002_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 830 10 10, g32p_row17_traceSegment_002_0830_0010, g32p_row17_traceSegment_002_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 810 20 20, g32p_row17_traceSegment_002_0810_0020, g32p_row17_traceSegment_002_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 850 10 10, g32p_row17_traceSegment_002_0850_0010, g32p_row17_traceSegment_002_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 870 10 11, g32p_row17_traceSegment_002_0870_0010, g32p_row17_traceSegment_002_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 850 20 21, g32p_row17_traceSegment_002_0850_0020, g32p_row17_traceSegment_002_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 810 40 41, g32p_row17_traceSegment_002_0810_0040, g32p_row17_traceSegment_002_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 891 10 10, g32p_row17_traceSegment_002_0891_0010, g32p_row17_traceSegment_002_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 911 10 10, g32p_row17_traceSegment_002_0911_0010, g32p_row17_traceSegment_002_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 891 20 20, g32p_row17_traceSegment_002_0891_0020, g32p_row17_traceSegment_002_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 931 10 10, g32p_row17_traceSegment_002_0931_0010, g32p_row17_traceSegment_002_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 951 10 11, g32p_row17_traceSegment_002_0951_0010, g32p_row17_traceSegment_002_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 931 20 21, g32p_row17_traceSegment_002_0931_0020, g32p_row17_traceSegment_002_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 891 40 41, g32p_row17_traceSegment_002_0891_0040, g32p_row17_traceSegment_002_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_002 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 810 81 81, g32p_row17_traceSegment_002_0810_0081, g32p_row17_traceSegment_002_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_002 648 324 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 648 162 162, g32p_row17_traceSegment_002_0648_0162, g32p_row17_traceSegment_002_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 972 10 10, g32p_row17_traceSegment_002_0972_0010, g32p_row17_traceSegment_002_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 992 10 10, g32p_row17_traceSegment_002_0992_0010, g32p_row17_traceSegment_002_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 972 20 20, g32p_row17_traceSegment_002_0972_0020, g32p_row17_traceSegment_002_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1012 10 10, g32p_row17_traceSegment_002_1012_0010, g32p_row17_traceSegment_002_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1032 10 11, g32p_row17_traceSegment_002_1032_0010, g32p_row17_traceSegment_002_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1012 20 21, g32p_row17_traceSegment_002_1012_0020, g32p_row17_traceSegment_002_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 972 40 41, g32p_row17_traceSegment_002_0972_0040, g32p_row17_traceSegment_002_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1053 10 10, g32p_row17_traceSegment_002_1053_0010, g32p_row17_traceSegment_002_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1073 10 10, g32p_row17_traceSegment_002_1073_0010, g32p_row17_traceSegment_002_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1053 20 20, g32p_row17_traceSegment_002_1053_0020, g32p_row17_traceSegment_002_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1093 10 10, g32p_row17_traceSegment_002_1093_0010, g32p_row17_traceSegment_002_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1113 10 11, g32p_row17_traceSegment_002_1113_0010, g32p_row17_traceSegment_002_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1093 20 21, g32p_row17_traceSegment_002_1093_0020, g32p_row17_traceSegment_002_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1053 40 41, g32p_row17_traceSegment_002_1053_0040, g32p_row17_traceSegment_002_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_002 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 972 81 81, g32p_row17_traceSegment_002_0972_0081, g32p_row17_traceSegment_002_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1134 10 10, g32p_row17_traceSegment_002_1134_0010, g32p_row17_traceSegment_002_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1154 10 10, g32p_row17_traceSegment_002_1154_0010, g32p_row17_traceSegment_002_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 1134 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1134 20 20, g32p_row17_traceSegment_002_1134_0020, g32p_row17_traceSegment_002_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1174 10 10, g32p_row17_traceSegment_002_1174_0010, g32p_row17_traceSegment_002_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1194 10 11, g32p_row17_traceSegment_002_1194_0010, g32p_row17_traceSegment_002_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1174 20 21, g32p_row17_traceSegment_002_1174_0020, g32p_row17_traceSegment_002_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 1134 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1134 40 41, g32p_row17_traceSegment_002_1134_0040, g32p_row17_traceSegment_002_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1215 10 10, g32p_row17_traceSegment_002_1215_0010, g32p_row17_traceSegment_002_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1235 10 10, g32p_row17_traceSegment_002_1235_0010, g32p_row17_traceSegment_002_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_002 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1215 20 20, g32p_row17_traceSegment_002_1215_0020, g32p_row17_traceSegment_002_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_002 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1255 10 10, g32p_row17_traceSegment_002_1255_0010, g32p_row17_traceSegment_002_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_002 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_002 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_002_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_002 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1275 10 11, g32p_row17_traceSegment_002_1275_0010, g32p_row17_traceSegment_002_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_002 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1255 20 21, g32p_row17_traceSegment_002_1255_0020, g32p_row17_traceSegment_002_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_002 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1215 40 41, g32p_row17_traceSegment_002_1215_0040, g32p_row17_traceSegment_002_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_002_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_002 1134 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 1134 81 81, g32p_row17_traceSegment_002_1134_0081, g32p_row17_traceSegment_002_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_002 972 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 972 162 162, g32p_row17_traceSegment_002_0972_0162, g32p_row17_traceSegment_002_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_002 648 648 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 648 324 324, g32p_row17_traceSegment_002_0648_0324, g32p_row17_traceSegment_002_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_002_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_002 0 1296 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_002 0 648 648, g32p_row17_traceSegment_002_0000_0648, g32p_row17_traceSegment_002_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 2 = [0, 0, 0, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_002_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_003 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 3 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_003_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 0 10 10, g32p_row17_traceSegment_003_0000_0010, g32p_row17_traceSegment_003_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 20 10 10, g32p_row17_traceSegment_003_0020_0010, g32p_row17_traceSegment_003_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 0 20 20, g32p_row17_traceSegment_003_0000_0020, g32p_row17_traceSegment_003_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 40 10 10, g32p_row17_traceSegment_003_0040_0010, g32p_row17_traceSegment_003_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 70 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 60 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 60 10 11, g32p_row17_traceSegment_003_0060_0010, g32p_row17_traceSegment_003_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 40 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 40 20 21, g32p_row17_traceSegment_003_0040_0020, g32p_row17_traceSegment_003_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 0 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 0 40 41, g32p_row17_traceSegment_003_0000_0040, g32p_row17_traceSegment_003_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 81 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 81 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 81 10 10, g32p_row17_traceSegment_003_0081_0010, g32p_row17_traceSegment_003_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 101 10 10, g32p_row17_traceSegment_003_0101_0010, g32p_row17_traceSegment_003_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 81 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 81 20 20, g32p_row17_traceSegment_003_0081_0020, g32p_row17_traceSegment_003_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 131 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 121 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 121 10 10, g32p_row17_traceSegment_003_0121_0010, g32p_row17_traceSegment_003_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 151 11 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 141 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 141 10 11, g32p_row17_traceSegment_003_0141_0010, g32p_row17_traceSegment_003_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 121 41 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 121 20 21, g32p_row17_traceSegment_003_0121_0020, g32p_row17_traceSegment_003_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 81 81 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 81 40 41, g32p_row17_traceSegment_003_0081_0040, g32p_row17_traceSegment_003_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_003 0 162 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 0 81 81, g32p_row17_traceSegment_003_0000_0081, g32p_row17_traceSegment_003_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 162 10 10, g32p_row17_traceSegment_003_0162_0010, g32p_row17_traceSegment_003_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 182 10 10, g32p_row17_traceSegment_003_0182_0010, g32p_row17_traceSegment_003_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 162 20 20, g32p_row17_traceSegment_003_0162_0020, g32p_row17_traceSegment_003_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 202 10 10, g32p_row17_traceSegment_003_0202_0010, g32p_row17_traceSegment_003_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 222 10 11, g32p_row17_traceSegment_003_0222_0010, g32p_row17_traceSegment_003_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 202 20 21, g32p_row17_traceSegment_003_0202_0020, g32p_row17_traceSegment_003_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 162 40 41, g32p_row17_traceSegment_003_0162_0040, g32p_row17_traceSegment_003_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 253 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 243 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 243 10 10, g32p_row17_traceSegment_003_0243_0010, g32p_row17_traceSegment_003_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 263 10 10, g32p_row17_traceSegment_003_0263_0010, g32p_row17_traceSegment_003_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 243 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 243 20 20, g32p_row17_traceSegment_003_0243_0020, g32p_row17_traceSegment_003_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 283 10 10, g32p_row17_traceSegment_003_0283_0010, g32p_row17_traceSegment_003_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 303 10 11, g32p_row17_traceSegment_003_0303_0010, g32p_row17_traceSegment_003_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 283 20 21, g32p_row17_traceSegment_003_0283_0020, g32p_row17_traceSegment_003_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 243 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 243 40 41, g32p_row17_traceSegment_003_0243_0040, g32p_row17_traceSegment_003_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_003 162 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 162 81 81, g32p_row17_traceSegment_003_0162_0081, g32p_row17_traceSegment_003_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_003 0 324 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 0 162 162, g32p_row17_traceSegment_003_0000_0162, g32p_row17_traceSegment_003_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 324 10 10, g32p_row17_traceSegment_003_0324_0010, g32p_row17_traceSegment_003_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 344 10 10, g32p_row17_traceSegment_003_0344_0010, g32p_row17_traceSegment_003_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 324 20 20, g32p_row17_traceSegment_003_0324_0020, g32p_row17_traceSegment_003_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 364 10 10, g32p_row17_traceSegment_003_0364_0010, g32p_row17_traceSegment_003_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 384 10 11, g32p_row17_traceSegment_003_0384_0010, g32p_row17_traceSegment_003_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 364 20 21, g32p_row17_traceSegment_003_0364_0020, g32p_row17_traceSegment_003_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 324 40 41, g32p_row17_traceSegment_003_0324_0040, g32p_row17_traceSegment_003_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 405 10 10, g32p_row17_traceSegment_003_0405_0010, g32p_row17_traceSegment_003_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 425 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 425 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 425 10 10, g32p_row17_traceSegment_003_0425_0010, g32p_row17_traceSegment_003_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 405 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 405 20 20, g32p_row17_traceSegment_003_0405_0020, g32p_row17_traceSegment_003_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 445 10 10, g32p_row17_traceSegment_003_0445_0010, g32p_row17_traceSegment_003_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 465 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 465 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 465 10 11, g32p_row17_traceSegment_003_0465_0010, g32p_row17_traceSegment_003_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 445 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 445 20 21, g32p_row17_traceSegment_003_0445_0020, g32p_row17_traceSegment_003_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 405 81 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 405 40 41, g32p_row17_traceSegment_003_0405_0040, g32p_row17_traceSegment_003_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_003 324 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 324 81 81, g32p_row17_traceSegment_003_0324_0081, g32p_row17_traceSegment_003_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 486 10 10, g32p_row17_traceSegment_003_0486_0010, g32p_row17_traceSegment_003_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 506 10 10, g32p_row17_traceSegment_003_0506_0010, g32p_row17_traceSegment_003_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 486 20 20, g32p_row17_traceSegment_003_0486_0020, g32p_row17_traceSegment_003_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 526 10 10, g32p_row17_traceSegment_003_0526_0010, g32p_row17_traceSegment_003_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 546 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 546 21 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 546 10 11, g32p_row17_traceSegment_003_0546_0010, g32p_row17_traceSegment_003_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 526 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 526 20 21, g32p_row17_traceSegment_003_0526_0020, g32p_row17_traceSegment_003_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 486 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 486 40 41, g32p_row17_traceSegment_003_0486_0040, g32p_row17_traceSegment_003_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 567 10 10, g32p_row17_traceSegment_003_0567_0010, g32p_row17_traceSegment_003_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 587 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 587 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 587 10 10, g32p_row17_traceSegment_003_0587_0010, g32p_row17_traceSegment_003_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 567 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 567 20 20, g32p_row17_traceSegment_003_0567_0020, g32p_row17_traceSegment_003_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 607 10 10, g32p_row17_traceSegment_003_0607_0010, g32p_row17_traceSegment_003_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 627 10 11, g32p_row17_traceSegment_003_0627_0010, g32p_row17_traceSegment_003_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 607 20 21, g32p_row17_traceSegment_003_0607_0020, g32p_row17_traceSegment_003_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 567 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 567 40 41, g32p_row17_traceSegment_003_0567_0040, g32p_row17_traceSegment_003_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_003 486 162 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 486 81 81, g32p_row17_traceSegment_003_0486_0081, g32p_row17_traceSegment_003_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_003 324 324 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 324 162 162, g32p_row17_traceSegment_003_0324_0162, g32p_row17_traceSegment_003_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_003 0 648 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 0 324 324, g32p_row17_traceSegment_003_0000_0324, g32p_row17_traceSegment_003_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 648 10 10, g32p_row17_traceSegment_003_0648_0010, g32p_row17_traceSegment_003_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 668 10 10, g32p_row17_traceSegment_003_0668_0010, g32p_row17_traceSegment_003_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 648 20 20, g32p_row17_traceSegment_003_0648_0020, g32p_row17_traceSegment_003_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 698 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 688 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 688 10 10, g32p_row17_traceSegment_003_0688_0010, g32p_row17_traceSegment_003_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 708 10 11, g32p_row17_traceSegment_003_0708_0010, g32p_row17_traceSegment_003_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 688 41 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 688 20 21, g32p_row17_traceSegment_003_0688_0020, g32p_row17_traceSegment_003_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 648 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 648 40 41, g32p_row17_traceSegment_003_0648_0040, g32p_row17_traceSegment_003_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 729 10 10, g32p_row17_traceSegment_003_0729_0010, g32p_row17_traceSegment_003_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 749 10 10, g32p_row17_traceSegment_003_0749_0010, g32p_row17_traceSegment_003_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 729 20 20, g32p_row17_traceSegment_003_0729_0020, g32p_row17_traceSegment_003_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 769 10 10, g32p_row17_traceSegment_003_0769_0010, g32p_row17_traceSegment_003_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 789 10 11, g32p_row17_traceSegment_003_0789_0010, g32p_row17_traceSegment_003_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 769 20 21, g32p_row17_traceSegment_003_0769_0020, g32p_row17_traceSegment_003_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 729 40 41, g32p_row17_traceSegment_003_0729_0040, g32p_row17_traceSegment_003_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_003 648 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 648 81 81, g32p_row17_traceSegment_003_0648_0081, g32p_row17_traceSegment_003_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 810 10 10, g32p_row17_traceSegment_003_0810_0010, g32p_row17_traceSegment_003_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 830 10 10, g32p_row17_traceSegment_003_0830_0010, g32p_row17_traceSegment_003_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 810 20 20, g32p_row17_traceSegment_003_0810_0020, g32p_row17_traceSegment_003_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 850 10 10, g32p_row17_traceSegment_003_0850_0010, g32p_row17_traceSegment_003_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 870 10 11, g32p_row17_traceSegment_003_0870_0010, g32p_row17_traceSegment_003_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 850 20 21, g32p_row17_traceSegment_003_0850_0020, g32p_row17_traceSegment_003_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 810 40 41, g32p_row17_traceSegment_003_0810_0040, g32p_row17_traceSegment_003_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 891 10 10, g32p_row17_traceSegment_003_0891_0010, g32p_row17_traceSegment_003_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 911 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 911 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 911 10 10, g32p_row17_traceSegment_003_0911_0010, g32p_row17_traceSegment_003_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 891 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 891 20 20, g32p_row17_traceSegment_003_0891_0020, g32p_row17_traceSegment_003_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 931 10 10, g32p_row17_traceSegment_003_0931_0010, g32p_row17_traceSegment_003_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 951 10 11, g32p_row17_traceSegment_003_0951_0010, g32p_row17_traceSegment_003_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 931 20 21, g32p_row17_traceSegment_003_0931_0020, g32p_row17_traceSegment_003_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 891 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 891 40 41, g32p_row17_traceSegment_003_0891_0040, g32p_row17_traceSegment_003_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_003 810 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 810 81 81, g32p_row17_traceSegment_003_0810_0081, g32p_row17_traceSegment_003_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_003 648 324 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 648 162 162, g32p_row17_traceSegment_003_0648_0162, g32p_row17_traceSegment_003_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 972 10 10, g32p_row17_traceSegment_003_0972_0010, g32p_row17_traceSegment_003_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 992 10 10, g32p_row17_traceSegment_003_0992_0010, g32p_row17_traceSegment_003_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 972 20 20, g32p_row17_traceSegment_003_0972_0020, g32p_row17_traceSegment_003_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1012 10 10, g32p_row17_traceSegment_003_1012_0010, g32p_row17_traceSegment_003_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1032 10 11, g32p_row17_traceSegment_003_1032_0010, g32p_row17_traceSegment_003_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1012 20 21, g32p_row17_traceSegment_003_1012_0020, g32p_row17_traceSegment_003_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 972 40 41, g32p_row17_traceSegment_003_0972_0040, g32p_row17_traceSegment_003_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1053 10 10, g32p_row17_traceSegment_003_1053_0010, g32p_row17_traceSegment_003_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1073 10 10, g32p_row17_traceSegment_003_1073_0010, g32p_row17_traceSegment_003_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 1053 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1053 20 20, g32p_row17_traceSegment_003_1053_0020, g32p_row17_traceSegment_003_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1093 10 10, g32p_row17_traceSegment_003_1093_0010, g32p_row17_traceSegment_003_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1113 10 11, g32p_row17_traceSegment_003_1113_0010, g32p_row17_traceSegment_003_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1093 20 21, g32p_row17_traceSegment_003_1093_0020, g32p_row17_traceSegment_003_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 1053 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1053 40 41, g32p_row17_traceSegment_003_1053_0040, g32p_row17_traceSegment_003_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_003 972 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 972 81 81, g32p_row17_traceSegment_003_0972_0081, g32p_row17_traceSegment_003_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1134 10 10, g32p_row17_traceSegment_003_1134_0010, g32p_row17_traceSegment_003_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1154 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1154 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1154 10 10, g32p_row17_traceSegment_003_1154_0010, g32p_row17_traceSegment_003_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 1134 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1134 20 20, g32p_row17_traceSegment_003_1134_0020, g32p_row17_traceSegment_003_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1174 10 10, g32p_row17_traceSegment_003_1174_0010, g32p_row17_traceSegment_003_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1194 10 11, g32p_row17_traceSegment_003_1194_0010, g32p_row17_traceSegment_003_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1174 20 21, g32p_row17_traceSegment_003_1174_0020, g32p_row17_traceSegment_003_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 1134 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1134 40 41, g32p_row17_traceSegment_003_1134_0040, g32p_row17_traceSegment_003_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1215 10 10, g32p_row17_traceSegment_003_1215_0010, g32p_row17_traceSegment_003_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1235 10 10, g32p_row17_traceSegment_003_1235_0010, g32p_row17_traceSegment_003_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_003 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1215 20 20, g32p_row17_traceSegment_003_1215_0020, g32p_row17_traceSegment_003_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_003 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1255 10 10, g32p_row17_traceSegment_003_1255_0010, g32p_row17_traceSegment_003_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_003 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_003 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_003_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_003 1275 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1275 10 11, g32p_row17_traceSegment_003_1275_0010, g32p_row17_traceSegment_003_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_003 1255 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1255 20 21, g32p_row17_traceSegment_003_1255_0020, g32p_row17_traceSegment_003_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_003 1215 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1215 40 41, g32p_row17_traceSegment_003_1215_0040, g32p_row17_traceSegment_003_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_003_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_003 1134 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 1134 81 81, g32p_row17_traceSegment_003_1134_0081, g32p_row17_traceSegment_003_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_003 972 324 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 972 162 162, g32p_row17_traceSegment_003_0972_0162, g32p_row17_traceSegment_003_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_003 648 648 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 648 324 324, g32p_row17_traceSegment_003_0648_0324, g32p_row17_traceSegment_003_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_003_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_003 0 1296 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_003 0 648 648, g32p_row17_traceSegment_003_0000_0648, g32p_row17_traceSegment_003_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 3 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_003_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_004 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 4 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_004_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 10 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 0 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 0 10 10, g32p_row17_traceSegment_004_0000_0010, g32p_row17_traceSegment_004_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 20 10 10, g32p_row17_traceSegment_004_0020_0010, g32p_row17_traceSegment_004_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 0 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 0 20 20, g32p_row17_traceSegment_004_0000_0020, g32p_row17_traceSegment_004_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 40 10 10, g32p_row17_traceSegment_004_0040_0010, g32p_row17_traceSegment_004_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 60 10 11, g32p_row17_traceSegment_004_0060_0010, g32p_row17_traceSegment_004_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 40 20 21, g32p_row17_traceSegment_004_0040_0020, g32p_row17_traceSegment_004_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 0 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 0 40 41, g32p_row17_traceSegment_004_0000_0040, g32p_row17_traceSegment_004_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 81 10 10, g32p_row17_traceSegment_004_0081_0010, g32p_row17_traceSegment_004_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 101 10 10, g32p_row17_traceSegment_004_0101_0010, g32p_row17_traceSegment_004_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 81 20 20, g32p_row17_traceSegment_004_0081_0020, g32p_row17_traceSegment_004_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 131 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 121 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 121 10 10, g32p_row17_traceSegment_004_0121_0010, g32p_row17_traceSegment_004_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 141 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 141 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 141 10 11, g32p_row17_traceSegment_004_0141_0010, g32p_row17_traceSegment_004_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 121 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 121 20 21, g32p_row17_traceSegment_004_0121_0020, g32p_row17_traceSegment_004_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 81 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 81 40 41, g32p_row17_traceSegment_004_0081_0040, g32p_row17_traceSegment_004_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_004 0 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 0 81 81, g32p_row17_traceSegment_004_0000_0081, g32p_row17_traceSegment_004_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 172 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 162 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 162 10 10, g32p_row17_traceSegment_004_0162_0010, g32p_row17_traceSegment_004_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 182 10 10, g32p_row17_traceSegment_004_0182_0010, g32p_row17_traceSegment_004_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 162 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 162 20 20, g32p_row17_traceSegment_004_0162_0020, g32p_row17_traceSegment_004_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 212 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 202 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 202 10 10, g32p_row17_traceSegment_004_0202_0010, g32p_row17_traceSegment_004_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 222 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 222 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 222 10 11, g32p_row17_traceSegment_004_0222_0010, g32p_row17_traceSegment_004_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 202 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 202 20 21, g32p_row17_traceSegment_004_0202_0020, g32p_row17_traceSegment_004_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 162 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 162 40 41, g32p_row17_traceSegment_004_0162_0040, g32p_row17_traceSegment_004_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 243 10 10, g32p_row17_traceSegment_004_0243_0010, g32p_row17_traceSegment_004_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 273 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 263 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 263 10 10, g32p_row17_traceSegment_004_0263_0010, g32p_row17_traceSegment_004_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 243 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 243 20 20, g32p_row17_traceSegment_004_0243_0020, g32p_row17_traceSegment_004_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 283 10 10, g32p_row17_traceSegment_004_0283_0010, g32p_row17_traceSegment_004_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 303 10 11, g32p_row17_traceSegment_004_0303_0010, g32p_row17_traceSegment_004_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 283 20 21, g32p_row17_traceSegment_004_0283_0020, g32p_row17_traceSegment_004_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 243 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 243 40 41, g32p_row17_traceSegment_004_0243_0040, g32p_row17_traceSegment_004_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_004 162 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 162 81 81, g32p_row17_traceSegment_004_0162_0081, g32p_row17_traceSegment_004_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_004 0 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 0 162 162, g32p_row17_traceSegment_004_0000_0162, g32p_row17_traceSegment_004_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 324 10 10, g32p_row17_traceSegment_004_0324_0010, g32p_row17_traceSegment_004_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 344 10 10, g32p_row17_traceSegment_004_0344_0010, g32p_row17_traceSegment_004_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 324 20 20, g32p_row17_traceSegment_004_0324_0020, g32p_row17_traceSegment_004_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 364 10 10, g32p_row17_traceSegment_004_0364_0010, g32p_row17_traceSegment_004_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 384 10 11, g32p_row17_traceSegment_004_0384_0010, g32p_row17_traceSegment_004_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 364 20 21, g32p_row17_traceSegment_004_0364_0020, g32p_row17_traceSegment_004_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 324 40 41, g32p_row17_traceSegment_004_0324_0040, g32p_row17_traceSegment_004_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 405 10 10, g32p_row17_traceSegment_004_0405_0010, g32p_row17_traceSegment_004_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 425 10 10, g32p_row17_traceSegment_004_0425_0010, g32p_row17_traceSegment_004_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 405 20 20, g32p_row17_traceSegment_004_0405_0020, g32p_row17_traceSegment_004_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 445 10 10, g32p_row17_traceSegment_004_0445_0010, g32p_row17_traceSegment_004_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 465 10 11, g32p_row17_traceSegment_004_0465_0010, g32p_row17_traceSegment_004_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 445 20 21, g32p_row17_traceSegment_004_0445_0020, g32p_row17_traceSegment_004_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 405 40 41, g32p_row17_traceSegment_004_0405_0040, g32p_row17_traceSegment_004_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_004 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 324 81 81, g32p_row17_traceSegment_004_0324_0081, g32p_row17_traceSegment_004_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 486 10 10, g32p_row17_traceSegment_004_0486_0010, g32p_row17_traceSegment_004_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 506 10 10, g32p_row17_traceSegment_004_0506_0010, g32p_row17_traceSegment_004_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 486 20 20, g32p_row17_traceSegment_004_0486_0020, g32p_row17_traceSegment_004_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 526 10 10, g32p_row17_traceSegment_004_0526_0010, g32p_row17_traceSegment_004_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 546 10 11, g32p_row17_traceSegment_004_0546_0010, g32p_row17_traceSegment_004_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 526 20 21, g32p_row17_traceSegment_004_0526_0020, g32p_row17_traceSegment_004_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 486 40 41, g32p_row17_traceSegment_004_0486_0040, g32p_row17_traceSegment_004_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 567 10 10, g32p_row17_traceSegment_004_0567_0010, g32p_row17_traceSegment_004_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 587 10 10, g32p_row17_traceSegment_004_0587_0010, g32p_row17_traceSegment_004_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 567 20 20, g32p_row17_traceSegment_004_0567_0020, g32p_row17_traceSegment_004_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 607 10 10, g32p_row17_traceSegment_004_0607_0010, g32p_row17_traceSegment_004_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 627 10 11, g32p_row17_traceSegment_004_0627_0010, g32p_row17_traceSegment_004_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 607 20 21, g32p_row17_traceSegment_004_0607_0020, g32p_row17_traceSegment_004_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 567 40 41, g32p_row17_traceSegment_004_0567_0040, g32p_row17_traceSegment_004_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_004 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 486 81 81, g32p_row17_traceSegment_004_0486_0081, g32p_row17_traceSegment_004_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_004 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 324 162 162, g32p_row17_traceSegment_004_0324_0162, g32p_row17_traceSegment_004_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_004 0 648 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 0 324 324, g32p_row17_traceSegment_004_0000_0324, g32p_row17_traceSegment_004_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 648 10 10, g32p_row17_traceSegment_004_0648_0010, g32p_row17_traceSegment_004_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 668 10 10, g32p_row17_traceSegment_004_0668_0010, g32p_row17_traceSegment_004_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 648 20 20, g32p_row17_traceSegment_004_0648_0020, g32p_row17_traceSegment_004_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 688 10 10, g32p_row17_traceSegment_004_0688_0010, g32p_row17_traceSegment_004_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 708 10 11, g32p_row17_traceSegment_004_0708_0010, g32p_row17_traceSegment_004_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 688 20 21, g32p_row17_traceSegment_004_0688_0020, g32p_row17_traceSegment_004_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 648 40 41, g32p_row17_traceSegment_004_0648_0040, g32p_row17_traceSegment_004_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 729 10 10, g32p_row17_traceSegment_004_0729_0010, g32p_row17_traceSegment_004_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 749 10 10, g32p_row17_traceSegment_004_0749_0010, g32p_row17_traceSegment_004_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 729 20 20, g32p_row17_traceSegment_004_0729_0020, g32p_row17_traceSegment_004_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 769 10 10, g32p_row17_traceSegment_004_0769_0010, g32p_row17_traceSegment_004_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 789 10 11, g32p_row17_traceSegment_004_0789_0010, g32p_row17_traceSegment_004_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 769 20 21, g32p_row17_traceSegment_004_0769_0020, g32p_row17_traceSegment_004_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 729 40 41, g32p_row17_traceSegment_004_0729_0040, g32p_row17_traceSegment_004_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_004 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 648 81 81, g32p_row17_traceSegment_004_0648_0081, g32p_row17_traceSegment_004_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 810 10 10, g32p_row17_traceSegment_004_0810_0010, g32p_row17_traceSegment_004_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 830 10 10, g32p_row17_traceSegment_004_0830_0010, g32p_row17_traceSegment_004_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 810 20 20, g32p_row17_traceSegment_004_0810_0020, g32p_row17_traceSegment_004_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 850 10 10, g32p_row17_traceSegment_004_0850_0010, g32p_row17_traceSegment_004_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 870 10 11, g32p_row17_traceSegment_004_0870_0010, g32p_row17_traceSegment_004_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 850 20 21, g32p_row17_traceSegment_004_0850_0020, g32p_row17_traceSegment_004_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 810 40 41, g32p_row17_traceSegment_004_0810_0040, g32p_row17_traceSegment_004_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 891 10 10, g32p_row17_traceSegment_004_0891_0010, g32p_row17_traceSegment_004_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 911 10 10, g32p_row17_traceSegment_004_0911_0010, g32p_row17_traceSegment_004_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 891 20 20, g32p_row17_traceSegment_004_0891_0020, g32p_row17_traceSegment_004_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 931 10 10, g32p_row17_traceSegment_004_0931_0010, g32p_row17_traceSegment_004_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 951 10 11, g32p_row17_traceSegment_004_0951_0010, g32p_row17_traceSegment_004_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 931 20 21, g32p_row17_traceSegment_004_0931_0020, g32p_row17_traceSegment_004_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 891 40 41, g32p_row17_traceSegment_004_0891_0040, g32p_row17_traceSegment_004_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_004 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 810 81 81, g32p_row17_traceSegment_004_0810_0081, g32p_row17_traceSegment_004_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_004 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 648 162 162, g32p_row17_traceSegment_004_0648_0162, g32p_row17_traceSegment_004_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 972 10 10, g32p_row17_traceSegment_004_0972_0010, g32p_row17_traceSegment_004_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 992 10 10, g32p_row17_traceSegment_004_0992_0010, g32p_row17_traceSegment_004_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 972 20 20, g32p_row17_traceSegment_004_0972_0020, g32p_row17_traceSegment_004_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1012 10 10, g32p_row17_traceSegment_004_1012_0010, g32p_row17_traceSegment_004_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1032 10 11, g32p_row17_traceSegment_004_1032_0010, g32p_row17_traceSegment_004_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1012 20 21, g32p_row17_traceSegment_004_1012_0020, g32p_row17_traceSegment_004_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 972 40 41, g32p_row17_traceSegment_004_0972_0040, g32p_row17_traceSegment_004_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1063 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1053 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1053 10 10, g32p_row17_traceSegment_004_1053_0010, g32p_row17_traceSegment_004_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1073 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1073 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1073 10 10, g32p_row17_traceSegment_004_1073_0010, g32p_row17_traceSegment_004_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 1053 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1053 20 20, g32p_row17_traceSegment_004_1053_0020, g32p_row17_traceSegment_004_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1093 10 10, g32p_row17_traceSegment_004_1093_0010, g32p_row17_traceSegment_004_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1113 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 1113 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1113 10 11, g32p_row17_traceSegment_004_1113_0010, g32p_row17_traceSegment_004_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 1093 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1093 20 21, g32p_row17_traceSegment_004_1093_0020, g32p_row17_traceSegment_004_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 1053 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1053 40 41, g32p_row17_traceSegment_004_1053_0040, g32p_row17_traceSegment_004_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_004 972 162 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 972 81 81, g32p_row17_traceSegment_004_0972_0081, g32p_row17_traceSegment_004_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1134 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1134 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1134 10 10, g32p_row17_traceSegment_004_1134_0010, g32p_row17_traceSegment_004_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1154 10 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1154 20 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1154 10 10, g32p_row17_traceSegment_004_1154_0010, g32p_row17_traceSegment_004_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 1134 40 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1134 20 20, g32p_row17_traceSegment_004_1134_0020, g32p_row17_traceSegment_004_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1174 10 10, g32p_row17_traceSegment_004_1174_0010, g32p_row17_traceSegment_004_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1194 10 11, g32p_row17_traceSegment_004_1194_0010, g32p_row17_traceSegment_004_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1174 20 21, g32p_row17_traceSegment_004_1174_0020, g32p_row17_traceSegment_004_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 1134 81 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1134 40 41, g32p_row17_traceSegment_004_1134_0040, g32p_row17_traceSegment_004_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1215 10 10, g32p_row17_traceSegment_004_1215_0010, g32p_row17_traceSegment_004_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1235 10 10, g32p_row17_traceSegment_004_1235_0010, g32p_row17_traceSegment_004_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_004 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1215 20 20, g32p_row17_traceSegment_004_1215_0020, g32p_row17_traceSegment_004_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1265 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_004 1255 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1255 10 10, g32p_row17_traceSegment_004_1255_0010, g32p_row17_traceSegment_004_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_004 1275 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_004 1285 11 = [0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row17_traceSegment_004_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_004 1275 21 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1275 10 11, g32p_row17_traceSegment_004_1275_0010, g32p_row17_traceSegment_004_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_004 1255 41 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1255 20 21, g32p_row17_traceSegment_004_1255_0020, g32p_row17_traceSegment_004_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_004 1215 81 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1215 40 41, g32p_row17_traceSegment_004_1215_0040, g32p_row17_traceSegment_004_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_004_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_004 1134 162 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 1134 81 81, g32p_row17_traceSegment_004_1134_0081, g32p_row17_traceSegment_004_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_004 972 324 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 972 162 162, g32p_row17_traceSegment_004_0972_0162, g32p_row17_traceSegment_004_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_004 648 648 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 648 324 324, g32p_row17_traceSegment_004_0648_0324, g32p_row17_traceSegment_004_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_004_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_004 0 1296 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_004 0 648 648, g32p_row17_traceSegment_004_0000_0648, g32p_row17_traceSegment_004_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 4 = [0, 0, 0, 0, 6] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_004_0000_1296

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row17_traceSegment_006 (k : ℕ) : List ℤ :=
  if g32p_row17_supplierClassifier (Fin.ofNat 1296 k) = 6 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row17_characterValues (Fin.ofNat 1296 k))).val 1 else []

private theorem g32p_row17_traceSegment_006_0000_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 0 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0010_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 10 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0000_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 0 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 0 10 10, g32p_row17_traceSegment_006_0000_0010, g32p_row17_traceSegment_006_0010_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0020_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 20 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0030_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 30 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0020_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 20 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 20 10 10, g32p_row17_traceSegment_006_0020_0010, g32p_row17_traceSegment_006_0030_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0000_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 0 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 0 20 20, g32p_row17_traceSegment_006_0000_0020, g32p_row17_traceSegment_006_0020_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0040_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 40 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0050_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 50 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0040_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 40 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 40 10 10, g32p_row17_traceSegment_006_0040_0010, g32p_row17_traceSegment_006_0050_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0060_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 60 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0070_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 70 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0060_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 60 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 60 10 11, g32p_row17_traceSegment_006_0060_0010, g32p_row17_traceSegment_006_0070_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0040_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 40 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 40 20 21, g32p_row17_traceSegment_006_0040_0020, g32p_row17_traceSegment_006_0060_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0000_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 0 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 0 40 41, g32p_row17_traceSegment_006_0000_0040, g32p_row17_traceSegment_006_0040_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0081_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 81 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0091_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 91 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0081_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 81 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 81 10 10, g32p_row17_traceSegment_006_0081_0010, g32p_row17_traceSegment_006_0091_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0101_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 101 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0111_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 111 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0101_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 101 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 101 10 10, g32p_row17_traceSegment_006_0101_0010, g32p_row17_traceSegment_006_0111_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0081_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 81 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 81 20 20, g32p_row17_traceSegment_006_0081_0020, g32p_row17_traceSegment_006_0101_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0121_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 121 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0131_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 131 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0121_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 121 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 121 10 10, g32p_row17_traceSegment_006_0121_0010, g32p_row17_traceSegment_006_0131_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0141_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 141 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0151_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 151 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0141_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 141 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 141 10 11, g32p_row17_traceSegment_006_0141_0010, g32p_row17_traceSegment_006_0151_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0121_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 121 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 121 20 21, g32p_row17_traceSegment_006_0121_0020, g32p_row17_traceSegment_006_0141_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0081_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 81 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 81 40 41, g32p_row17_traceSegment_006_0081_0040, g32p_row17_traceSegment_006_0121_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0000_0162 : g32p_coeffSegment g32p_row17_traceSegment_006 0 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 0 81 81, g32p_row17_traceSegment_006_0000_0081, g32p_row17_traceSegment_006_0081_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0162_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 162 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0172_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 172 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0162_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 162 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 162 10 10, g32p_row17_traceSegment_006_0162_0010, g32p_row17_traceSegment_006_0172_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0182_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 182 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0192_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 192 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0182_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 182 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 182 10 10, g32p_row17_traceSegment_006_0182_0010, g32p_row17_traceSegment_006_0192_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0162_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 162 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 162 20 20, g32p_row17_traceSegment_006_0162_0020, g32p_row17_traceSegment_006_0182_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0202_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 202 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0212_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 212 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0202_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 202 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 202 10 10, g32p_row17_traceSegment_006_0202_0010, g32p_row17_traceSegment_006_0212_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0222_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 222 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0232_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 232 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0222_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 222 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 222 10 11, g32p_row17_traceSegment_006_0222_0010, g32p_row17_traceSegment_006_0232_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0202_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 202 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 202 20 21, g32p_row17_traceSegment_006_0202_0020, g32p_row17_traceSegment_006_0222_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0162_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 162 81 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 162 40 41, g32p_row17_traceSegment_006_0162_0040, g32p_row17_traceSegment_006_0202_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0243_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 243 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0253_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 253 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0243_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 243 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 243 10 10, g32p_row17_traceSegment_006_0243_0010, g32p_row17_traceSegment_006_0253_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0263_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 263 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0273_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 273 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0263_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 263 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 263 10 10, g32p_row17_traceSegment_006_0263_0010, g32p_row17_traceSegment_006_0273_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0243_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 243 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 243 20 20, g32p_row17_traceSegment_006_0243_0020, g32p_row17_traceSegment_006_0263_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0283_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 283 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0293_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 293 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0283_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 283 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 283 10 10, g32p_row17_traceSegment_006_0283_0010, g32p_row17_traceSegment_006_0293_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0303_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 303 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0313_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 313 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0303_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 303 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 303 10 11, g32p_row17_traceSegment_006_0303_0010, g32p_row17_traceSegment_006_0313_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0283_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 283 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 283 20 21, g32p_row17_traceSegment_006_0283_0020, g32p_row17_traceSegment_006_0303_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0243_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 243 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 243 40 41, g32p_row17_traceSegment_006_0243_0040, g32p_row17_traceSegment_006_0283_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0162_0162 : g32p_coeffSegment g32p_row17_traceSegment_006 162 162 = [4] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 162 81 81, g32p_row17_traceSegment_006_0162_0081, g32p_row17_traceSegment_006_0243_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0000_0324 : g32p_coeffSegment g32p_row17_traceSegment_006 0 324 = [7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 0 162 162, g32p_row17_traceSegment_006_0000_0162, g32p_row17_traceSegment_006_0162_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0324_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 324 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0334_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 334 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0324_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 324 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 324 10 10, g32p_row17_traceSegment_006_0324_0010, g32p_row17_traceSegment_006_0334_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0344_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 344 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0354_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 354 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0344_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 344 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 344 10 10, g32p_row17_traceSegment_006_0344_0010, g32p_row17_traceSegment_006_0354_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0324_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 324 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 324 20 20, g32p_row17_traceSegment_006_0324_0020, g32p_row17_traceSegment_006_0344_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0364_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 364 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0374_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 374 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0364_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 364 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 364 10 10, g32p_row17_traceSegment_006_0364_0010, g32p_row17_traceSegment_006_0374_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0384_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 384 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0394_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 394 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0384_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 384 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 384 10 11, g32p_row17_traceSegment_006_0384_0010, g32p_row17_traceSegment_006_0394_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0364_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 364 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 364 20 21, g32p_row17_traceSegment_006_0364_0020, g32p_row17_traceSegment_006_0384_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0324_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 324 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 324 40 41, g32p_row17_traceSegment_006_0324_0040, g32p_row17_traceSegment_006_0364_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0405_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 405 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0415_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 415 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0405_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 405 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 405 10 10, g32p_row17_traceSegment_006_0405_0010, g32p_row17_traceSegment_006_0415_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0425_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 425 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0435_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 435 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0425_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 425 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 425 10 10, g32p_row17_traceSegment_006_0425_0010, g32p_row17_traceSegment_006_0435_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0405_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 405 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 405 20 20, g32p_row17_traceSegment_006_0405_0020, g32p_row17_traceSegment_006_0425_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0445_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 445 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0455_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 455 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0445_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 445 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 445 10 10, g32p_row17_traceSegment_006_0445_0010, g32p_row17_traceSegment_006_0455_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0465_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 465 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0475_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 475 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0465_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 465 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 465 10 11, g32p_row17_traceSegment_006_0465_0010, g32p_row17_traceSegment_006_0475_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0445_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 445 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 445 20 21, g32p_row17_traceSegment_006_0445_0020, g32p_row17_traceSegment_006_0465_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0405_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 405 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 405 40 41, g32p_row17_traceSegment_006_0405_0040, g32p_row17_traceSegment_006_0445_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0324_0162 : g32p_coeffSegment g32p_row17_traceSegment_006 324 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 324 81 81, g32p_row17_traceSegment_006_0324_0081, g32p_row17_traceSegment_006_0405_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0486_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 486 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0496_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 496 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0486_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 486 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 486 10 10, g32p_row17_traceSegment_006_0486_0010, g32p_row17_traceSegment_006_0496_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0506_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 506 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0516_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 516 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0506_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 506 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 506 10 10, g32p_row17_traceSegment_006_0506_0010, g32p_row17_traceSegment_006_0516_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0486_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 486 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 486 20 20, g32p_row17_traceSegment_006_0486_0020, g32p_row17_traceSegment_006_0506_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0526_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 526 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0536_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 536 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0526_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 526 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 526 10 10, g32p_row17_traceSegment_006_0526_0010, g32p_row17_traceSegment_006_0536_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0546_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 546 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0556_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 556 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0546_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 546 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 546 10 11, g32p_row17_traceSegment_006_0546_0010, g32p_row17_traceSegment_006_0556_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0526_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 526 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 526 20 21, g32p_row17_traceSegment_006_0526_0020, g32p_row17_traceSegment_006_0546_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0486_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 486 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 486 40 41, g32p_row17_traceSegment_006_0486_0040, g32p_row17_traceSegment_006_0526_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0567_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 567 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0577_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 577 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0567_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 567 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 567 10 10, g32p_row17_traceSegment_006_0567_0010, g32p_row17_traceSegment_006_0577_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0587_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 587 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0597_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 597 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0587_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 587 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 587 10 10, g32p_row17_traceSegment_006_0587_0010, g32p_row17_traceSegment_006_0597_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0567_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 567 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 567 20 20, g32p_row17_traceSegment_006_0567_0020, g32p_row17_traceSegment_006_0587_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0607_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 607 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0617_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 617 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0607_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 607 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 607 10 10, g32p_row17_traceSegment_006_0607_0010, g32p_row17_traceSegment_006_0617_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0627_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 627 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0637_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 637 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0627_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 627 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 627 10 11, g32p_row17_traceSegment_006_0627_0010, g32p_row17_traceSegment_006_0637_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0607_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 607 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 607 20 21, g32p_row17_traceSegment_006_0607_0020, g32p_row17_traceSegment_006_0627_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0567_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 567 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 567 40 41, g32p_row17_traceSegment_006_0567_0040, g32p_row17_traceSegment_006_0607_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0486_0162 : g32p_coeffSegment g32p_row17_traceSegment_006 486 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 486 81 81, g32p_row17_traceSegment_006_0486_0081, g32p_row17_traceSegment_006_0567_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0324_0324 : g32p_coeffSegment g32p_row17_traceSegment_006 324 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 324 162 162, g32p_row17_traceSegment_006_0324_0162, g32p_row17_traceSegment_006_0486_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0000_0648 : g32p_coeffSegment g32p_row17_traceSegment_006 0 648 = [7] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 0 324 324, g32p_row17_traceSegment_006_0000_0324, g32p_row17_traceSegment_006_0324_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0648_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 648 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0658_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 658 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0648_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 648 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 648 10 10, g32p_row17_traceSegment_006_0648_0010, g32p_row17_traceSegment_006_0658_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0668_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 668 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0678_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 678 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0668_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 668 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 668 10 10, g32p_row17_traceSegment_006_0668_0010, g32p_row17_traceSegment_006_0678_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0648_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 648 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 648 20 20, g32p_row17_traceSegment_006_0648_0020, g32p_row17_traceSegment_006_0668_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0688_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 688 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0698_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 698 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0688_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 688 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 688 10 10, g32p_row17_traceSegment_006_0688_0010, g32p_row17_traceSegment_006_0698_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0708_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 708 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0718_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 718 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0708_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 708 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 708 10 11, g32p_row17_traceSegment_006_0708_0010, g32p_row17_traceSegment_006_0718_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0688_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 688 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 688 20 21, g32p_row17_traceSegment_006_0688_0020, g32p_row17_traceSegment_006_0708_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0648_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 648 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 648 40 41, g32p_row17_traceSegment_006_0648_0040, g32p_row17_traceSegment_006_0688_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0729_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 729 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0739_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 739 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0729_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 729 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 729 10 10, g32p_row17_traceSegment_006_0729_0010, g32p_row17_traceSegment_006_0739_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0749_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 749 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0759_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 759 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0749_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 749 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 749 10 10, g32p_row17_traceSegment_006_0749_0010, g32p_row17_traceSegment_006_0759_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0729_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 729 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 729 20 20, g32p_row17_traceSegment_006_0729_0020, g32p_row17_traceSegment_006_0749_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0769_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 769 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0779_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 779 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0769_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 769 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 769 10 10, g32p_row17_traceSegment_006_0769_0010, g32p_row17_traceSegment_006_0779_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0789_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 789 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0799_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 799 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0789_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 789 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 789 10 11, g32p_row17_traceSegment_006_0789_0010, g32p_row17_traceSegment_006_0799_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0769_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 769 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 769 20 21, g32p_row17_traceSegment_006_0769_0020, g32p_row17_traceSegment_006_0789_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0729_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 729 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 729 40 41, g32p_row17_traceSegment_006_0729_0040, g32p_row17_traceSegment_006_0769_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0648_0162 : g32p_coeffSegment g32p_row17_traceSegment_006 648 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 648 81 81, g32p_row17_traceSegment_006_0648_0081, g32p_row17_traceSegment_006_0729_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0810_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 810 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0820_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 820 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0810_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 810 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 810 10 10, g32p_row17_traceSegment_006_0810_0010, g32p_row17_traceSegment_006_0820_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0830_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 830 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0840_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 840 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0830_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 830 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 830 10 10, g32p_row17_traceSegment_006_0830_0010, g32p_row17_traceSegment_006_0840_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0810_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 810 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 810 20 20, g32p_row17_traceSegment_006_0810_0020, g32p_row17_traceSegment_006_0830_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0850_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 850 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0860_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 860 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0850_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 850 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 850 10 10, g32p_row17_traceSegment_006_0850_0010, g32p_row17_traceSegment_006_0860_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0870_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 870 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0880_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 880 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0870_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 870 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 870 10 11, g32p_row17_traceSegment_006_0870_0010, g32p_row17_traceSegment_006_0880_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0850_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 850 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 850 20 21, g32p_row17_traceSegment_006_0850_0020, g32p_row17_traceSegment_006_0870_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0810_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 810 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 810 40 41, g32p_row17_traceSegment_006_0810_0040, g32p_row17_traceSegment_006_0850_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0891_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 891 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0901_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 901 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0891_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 891 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 891 10 10, g32p_row17_traceSegment_006_0891_0010, g32p_row17_traceSegment_006_0901_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0911_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 911 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0921_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 921 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0911_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 911 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 911 10 10, g32p_row17_traceSegment_006_0911_0010, g32p_row17_traceSegment_006_0921_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0891_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 891 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 891 20 20, g32p_row17_traceSegment_006_0891_0020, g32p_row17_traceSegment_006_0911_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0931_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 931 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0941_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 941 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0931_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 931 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 931 10 10, g32p_row17_traceSegment_006_0931_0010, g32p_row17_traceSegment_006_0941_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0951_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 951 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0961_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 961 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0951_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 951 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 951 10 11, g32p_row17_traceSegment_006_0951_0010, g32p_row17_traceSegment_006_0961_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0931_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 931 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 931 20 21, g32p_row17_traceSegment_006_0931_0020, g32p_row17_traceSegment_006_0951_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0891_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 891 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 891 40 41, g32p_row17_traceSegment_006_0891_0040, g32p_row17_traceSegment_006_0931_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0810_0162 : g32p_coeffSegment g32p_row17_traceSegment_006 810 162 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 810 81 81, g32p_row17_traceSegment_006_0810_0081, g32p_row17_traceSegment_006_0891_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0648_0324 : g32p_coeffSegment g32p_row17_traceSegment_006 648 324 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 648 162 162, g32p_row17_traceSegment_006_0648_0162, g32p_row17_traceSegment_006_0810_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0972_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 972 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0982_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 982 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0972_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 972 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 972 10 10, g32p_row17_traceSegment_006_0972_0010, g32p_row17_traceSegment_006_0982_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0992_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 992 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1002_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1002 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_0992_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 992 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 992 10 10, g32p_row17_traceSegment_006_0992_0010, g32p_row17_traceSegment_006_1002_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0972_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 972 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 972 20 20, g32p_row17_traceSegment_006_0972_0020, g32p_row17_traceSegment_006_0992_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1012_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1012 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1022_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1022 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1012_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1012 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1012 10 10, g32p_row17_traceSegment_006_1012_0010, g32p_row17_traceSegment_006_1022_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1032_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1032 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1042_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 1042 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1032_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 1032 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1032 10 11, g32p_row17_traceSegment_006_1032_0010, g32p_row17_traceSegment_006_1042_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1012_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 1012 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1012 20 21, g32p_row17_traceSegment_006_1012_0020, g32p_row17_traceSegment_006_1032_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0972_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 972 81 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 972 40 41, g32p_row17_traceSegment_006_0972_0040, g32p_row17_traceSegment_006_1012_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1053_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1053 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1063_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1063 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1053_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1053 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1053 10 10, g32p_row17_traceSegment_006_1053_0010, g32p_row17_traceSegment_006_1063_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1073_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1073 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1083_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1083 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1073_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1073 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1073 10 10, g32p_row17_traceSegment_006_1073_0010, g32p_row17_traceSegment_006_1083_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1053_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 1053 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1053 20 20, g32p_row17_traceSegment_006_1053_0020, g32p_row17_traceSegment_006_1073_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1093_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1093 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1103_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1103 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1093_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1093 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1093 10 10, g32p_row17_traceSegment_006_1093_0010, g32p_row17_traceSegment_006_1103_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1113_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1113 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1123_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 1123 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1113_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 1113 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1113 10 11, g32p_row17_traceSegment_006_1113_0010, g32p_row17_traceSegment_006_1123_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1093_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 1093 41 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1093 20 21, g32p_row17_traceSegment_006_1093_0020, g32p_row17_traceSegment_006_1113_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1053_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 1053 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1053 40 41, g32p_row17_traceSegment_006_1053_0040, g32p_row17_traceSegment_006_1093_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0972_0162 : g32p_coeffSegment g32p_row17_traceSegment_006 972 162 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 972 81 81, g32p_row17_traceSegment_006_0972_0081, g32p_row17_traceSegment_006_1053_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1134_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1134 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1144_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1144 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1134_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1134 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1134 10 10, g32p_row17_traceSegment_006_1134_0010, g32p_row17_traceSegment_006_1144_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1154_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1154 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1164_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1164 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1154_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1154 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1154 10 10, g32p_row17_traceSegment_006_1154_0010, g32p_row17_traceSegment_006_1164_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1134_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 1134 40 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1134 20 20, g32p_row17_traceSegment_006_1134_0020, g32p_row17_traceSegment_006_1154_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1174_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1174 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1184_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1184 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1174_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1174 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1174 10 10, g32p_row17_traceSegment_006_1174_0010, g32p_row17_traceSegment_006_1184_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1194_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1194 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1204_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 1204 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1194_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 1194 21 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1194 10 11, g32p_row17_traceSegment_006_1194_0010, g32p_row17_traceSegment_006_1204_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1174_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 1174 41 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1174 20 21, g32p_row17_traceSegment_006_1174_0020, g32p_row17_traceSegment_006_1194_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1134_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 1134 81 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1134 40 41, g32p_row17_traceSegment_006_1134_0040, g32p_row17_traceSegment_006_1174_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1215_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1215 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1225_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1225 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1215_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1215 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1215 10 10, g32p_row17_traceSegment_006_1215_0010, g32p_row17_traceSegment_006_1225_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1235_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1235 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1245_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1245 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1235_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1235 20 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1235 10 10, g32p_row17_traceSegment_006_1235_0010, g32p_row17_traceSegment_006_1245_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1215_0040 : g32p_coeffSegment g32p_row17_traceSegment_006 1215 40 = [] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1215 20 20, g32p_row17_traceSegment_006_1215_0020, g32p_row17_traceSegment_006_1235_0020]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1255_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1255 10 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1265_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1265 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1255_0020 : g32p_coeffSegment g32p_row17_traceSegment_006 1255 20 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1255 10 10, g32p_row17_traceSegment_006_1255_0010, g32p_row17_traceSegment_006_1265_0010]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1275_0010 : g32p_coeffSegment g32p_row17_traceSegment_006 1275 10 = [1] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1285_0011 : g32p_coeffSegment g32p_row17_traceSegment_006 1285 11 = [] := by
  decide +kernel

private theorem g32p_row17_traceSegment_006_1275_0021 : g32p_coeffSegment g32p_row17_traceSegment_006 1275 21 = [1] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1275 10 11, g32p_row17_traceSegment_006_1275_0010, g32p_row17_traceSegment_006_1285_0011]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1255_0041 : g32p_coeffSegment g32p_row17_traceSegment_006 1255 41 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1255 20 21, g32p_row17_traceSegment_006_1255_0020, g32p_row17_traceSegment_006_1275_0021]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1215_0081 : g32p_coeffSegment g32p_row17_traceSegment_006 1215 81 = [2] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1215 40 41, g32p_row17_traceSegment_006_1215_0040, g32p_row17_traceSegment_006_1255_0041]
  decide +kernel

private theorem g32p_row17_traceSegment_006_1134_0162 : g32p_coeffSegment g32p_row17_traceSegment_006 1134 162 = [3] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 1134 81 81, g32p_row17_traceSegment_006_1134_0081, g32p_row17_traceSegment_006_1215_0081]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0972_0324 : g32p_coeffSegment g32p_row17_traceSegment_006 972 324 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 972 162 162, g32p_row17_traceSegment_006_0972_0162, g32p_row17_traceSegment_006_1134_0162]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0648_0648 : g32p_coeffSegment g32p_row17_traceSegment_006 648 648 = [5] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 648 324 324, g32p_row17_traceSegment_006_0648_0324, g32p_row17_traceSegment_006_0972_0324]
  decide +kernel

private theorem g32p_row17_traceSegment_006_0000_1296 : g32p_coeffSegment g32p_row17_traceSegment_006 0 1296 = [12] := by
  rw [g32p_coeffSegment_add g32p_row17_traceSegment_006 0 648 648, g32p_row17_traceSegment_006_0000_0648, g32p_row17_traceSegment_006_0648_0648]
  decide +kernel

theorem g32p_row17_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row17_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row17_characterValues j)).val) 6 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row17_traceSegment_006_0000_1296

end HodgeLean.Foundations.Program

end
end
