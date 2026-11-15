import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0000 : Fin 8640 → Fin 8640 :=
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
7)
else
(if i.val < 3 then
13
else
14))
else
(if i.val < 6 then
(if i.val < 5 then
15
else
20)
else
(if i.val < 7 then
26
else
27)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
28
else
44)
else
(if i.val < 11 then
45
else
38))
else
(if i.val < 14 then
(if i.val < 13 then
46
else
47)
else
(if i.val < 15 then
0
else
48))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
49
else
50)
else
(if i.val < 19 then
51
else
63))
else
(if i.val < 22 then
(if i.val < 21 then
64
else
65)
else
(if i.val < 23 then
81
else
82)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
75
else
83)
else
(if i.val < 27 then
84
else
1))
else
(if i.val < 30 then
(if i.val < 29 then
85
else
86)
else
(if i.val < 31 then
87
else
88)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
128
else
113)
else
(if i.val < 35 then
129
else
130))
else
(if i.val < 38 then
(if i.val < 37 then
131
else
132)
else
(if i.val < 39 then
114
else
107)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
115
else
133)
else
(if i.val < 43 then
134
else
135))
else
(if i.val < 46 then
(if i.val < 45 then
136
else
137)
else
(if i.val < 47 then
138
else
2))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
4
else
139)
else
(if i.val < 51 then
140
else
141))
else
(if i.val < 54 then
(if i.val < 53 then
142
else
143)
else
(if i.val < 55 then
144
else
145)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
146
else
147)
else
(if i.val < 59 then
148
else
177))
else
(if i.val < 62 then
(if i.val < 61 then
178
else
171)
else
(if i.val < 63 then
179
else
180))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
5
else
181)
else
(if i.val < 67 then
182
else
183))
else
(if i.val < 70 then
(if i.val < 69 then
184
else
223)
else
(if i.val < 71 then
208
else
224)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
225
else
226)
else
(if i.val < 75 then
227
else
209))
else
(if i.val < 78 then
(if i.val < 77 then
202
else
210)
else
(if i.val < 79 then
228
else
229))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
230
else
231)
else
(if i.val < 83 then
232
else
233))
else
(if i.val < 86 then
(if i.val < 85 then
6
else
8)
else
(if i.val < 87 then
234
else
235)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
236
else
237)
else
(if i.val < 91 then
238
else
239))
else
(if i.val < 94 then
(if i.val < 93 then
240
else
241)
else
(if i.val < 95 then
242
else
243)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
299
else
335)
else
(if i.val < 99 then
265
else
285))
else
(if i.val < 102 then
(if i.val < 101 then
300
else
336)
else
(if i.val < 103 then
337
else
338)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
339
else
340)
else
(if i.val < 107 then
341
else
302))
else
(if i.val < 110 then
(if i.val < 109 then
288
else
342)
else
(if i.val < 111 then
343
else
344))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
345
else
301)
else
(if i.val < 115 then
11
else
303))
else
(if i.val < 118 then
(if i.val < 117 then
286
else
287)
else
(if i.val < 119 then
304
else
305)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
306
else
346)
else
(if i.val < 123 then
347
else
348))
else
(if i.val < 126 then
(if i.val < 125 then
349
else
350)
else
(if i.val < 127 then
351
else
352)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
353
else
354)
else
(if i.val < 131 then
355
else
308))
else
(if i.val < 134 then
(if i.val < 133 then
356
else
357)
else
(if i.val < 135 then
358
else
359)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
9
else
10)
else
(if i.val < 139 then
12
else
16))
else
(if i.val < 142 then
(if i.val < 141 then
17
else
18)
else
(if i.val < 143 then
360
else
361))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
362
else
363)
else
(if i.val < 147 then
364
else
365))
else
(if i.val < 150 then
(if i.val < 149 then
366
else
367)
else
(if i.val < 151 then
368
else
369)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
370
else
371)
else
(if i.val < 155 then
372
else
373))
else
(if i.val < 158 then
(if i.val < 157 then
374
else
375)
else
(if i.val < 159 then
376
else
377)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
378
else
379)
else
(if i.val < 163 then
380
else
381))
else
(if i.val < 166 then
(if i.val < 165 then
382
else
443)
else
(if i.val < 167 then
429
else
444)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
445
else
446)
else
(if i.val < 171 then
447
else
430))
else
(if i.val < 174 then
(if i.val < 173 then
423
else
431)
else
(if i.val < 175 then
448
else
449))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
450
else
451)
else
(if i.val < 179 then
452
else
453))
else
(if i.val < 182 then
(if i.val < 181 then
19
else
21)
else
(if i.val < 183 then
454
else
455)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
456
else
457)
else
(if i.val < 187 then
458
else
459))
else
(if i.val < 190 then
(if i.val < 189 then
460
else
461)
else
(if i.val < 191 then
462
else
463))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
517
else
552)
else
(if i.val < 195 then
485
else
504))
else
(if i.val < 198 then
(if i.val < 197 then
518
else
553)
else
(if i.val < 199 then
554
else
555)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
556
else
557)
else
(if i.val < 203 then
520
else
507))
else
(if i.val < 206 then
(if i.val < 205 then
558
else
559)
else
(if i.val < 207 then
560
else
561))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
519
else
24)
else
(if i.val < 211 then
521
else
505))
else
(if i.val < 214 then
(if i.val < 213 then
506
else
522)
else
(if i.val < 215 then
523
else
524)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
562
else
563)
else
(if i.val < 219 then
564
else
565))
else
(if i.val < 222 then
(if i.val < 221 then
566
else
567)
else
(if i.val < 223 then
568
else
569)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
570
else
571)
else
(if i.val < 227 then
526
else
572))
else
(if i.val < 230 then
(if i.val < 229 then
573
else
574)
else
(if i.val < 231 then
575
else
22)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
23
else
25)
else
(if i.val < 235 then
29
else
30))
else
(if i.val < 238 then
(if i.val < 237 then
31
else
576)
else
(if i.val < 239 then
577
else
578))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
579
else
580)
else
(if i.val < 243 then
581
else
582))
else
(if i.val < 246 then
(if i.val < 245 then
583
else
584)
else
(if i.val < 247 then
585
else
586)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
587
else
588)
else
(if i.val < 251 then
589
else
590))
else
(if i.val < 254 then
(if i.val < 253 then
591
else
592)
else
(if i.val < 255 then
593
else
594))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
595
else
596)
else
(if i.val < 259 then
597
else
806))
else
(if i.val < 262 then
(if i.val < 261 then
807
else
318)
else
(if i.val < 263 then
696
else
730)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
808
else
645)
else
(if i.val < 267 then
633
else
646))
else
(if i.val < 270 then
(if i.val < 269 then
683
else
697)
else
(if i.val < 271 then
731
else
732))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
733
else
809)
else
(if i.val < 275 then
810
else
811))
else
(if i.val < 278 then
(if i.val < 277 then
812
else
813)
else
(if i.val < 279 then
814
else
815)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
816
else
704)
else
(if i.val < 283 then
817
else
818))
else
(if i.val < 286 then
(if i.val < 285 then
819
else
735)
else
(if i.val < 287 then
699
else
737)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
705
else
706)
else
(if i.val < 291 then
820
else
821))
else
(if i.val < 294 then
(if i.val < 293 then
822
else
823)
else
(if i.val < 295 then
824
else
825)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
826
else
827)
else
(if i.val < 299 then
828
else
734))
else
(if i.val < 302 then
(if i.val < 301 then
736
else
33)
else
(if i.val < 303 then
39
else
40))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
738
else
739)
else
(if i.val < 307 then
740
else
698))
else
(if i.val < 310 then
(if i.val < 309 then
36
else
700)
else
(if i.val < 311 then
701
else
702)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
703
else
741)
else
(if i.val < 315 then
742
else
743))
else
(if i.val < 318 then
(if i.val < 317 then
744
else
745)
else
(if i.val < 319 then
746
else
747))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
829
else
830)
else
(if i.val < 323 then
831
else
832))
else
(if i.val < 326 then
(if i.val < 325 then
833
else
834)
else
(if i.val < 327 then
835
else
836)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
837
else
838)
else
(if i.val < 331 then
839
else
840))
else
(if i.val < 334 then
(if i.val < 333 then
841
else
842)
else
(if i.val < 335 then
843
else
844))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
845
else
846)
else
(if i.val < 339 then
847
else
848))
else
(if i.val < 342 then
(if i.val < 341 then
750
else
849)
else
(if i.val < 343 then
751
else
850)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
851
else
852)
else
(if i.val < 347 then
853
else
854))
else
(if i.val < 350 then
(if i.val < 349 then
855
else
856)
else
(if i.val < 351 then
857
else
858)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
859
else
32)
else
(if i.val < 355 then
34
else
35))
else
(if i.val < 358 then
(if i.val < 357 then
37
else
41)
else
(if i.val < 359 then
42
else
43)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
52
else
53)
else
(if i.val < 363 then
54
else
55))
else
(if i.val < 366 then
(if i.val < 365 then
56
else
57)
else
(if i.val < 367 then
58
else
860))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
861
else
862)
else
(if i.val < 371 then
863
else
864))
else
(if i.val < 374 then
(if i.val < 373 then
865
else
866)
else
(if i.val < 375 then
867
else
868)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
869
else
870)
else
(if i.val < 379 then
871
else
872))
else
(if i.val < 382 then
(if i.val < 381 then
873
else
874)
else
(if i.val < 383 then
875
else
876)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
400
else
877)
else
(if i.val < 387 then
878
else
879))
else
(if i.val < 390 then
(if i.val < 389 then
880
else
881)
else
(if i.val < 391 then
882
else
883)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
884
else
885)
else
(if i.val < 395 then
886
else
887))
else
(if i.val < 398 then
(if i.val < 397 then
888
else
889)
else
(if i.val < 399 then
890
else
891))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
892
else
893)
else
(if i.val < 403 then
894
else
895))
else
(if i.val < 406 then
(if i.val < 405 then
896
else
897)
else
(if i.val < 407 then
898
else
899)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
900
else
901)
else
(if i.val < 411 then
902
else
903))
else
(if i.val < 414 then
(if i.val < 413 then
904
else
905)
else
(if i.val < 415 then
1016
else
986)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
1004
else
1017)
else
(if i.val < 419 then
1048
else
1049))
else
(if i.val < 422 then
(if i.val < 421 then
1050
else
1051)
else
(if i.val < 423 then
1052
else
1019)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
1007
else
1053)
else
(if i.val < 427 then
1054
else
1055))
else
(if i.val < 430 then
(if i.val < 429 then
1056
else
1018)
else
(if i.val < 431 then
61
else
1020))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
1005
else
1006)
else
(if i.val < 435 then
1021
else
1022))
else
(if i.val < 438 then
(if i.val < 437 then
1023
else
1057)
else
(if i.val < 439 then
1058
else
1059)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
1060
else
1061)
else
(if i.val < 443 then
1062
else
1063))
else
(if i.val < 446 then
(if i.val < 445 then
1064
else
1065)
else
(if i.val < 447 then
1025
else
1066))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
1067
else
1068)
else
(if i.val < 451 then
1069
else
59))
else
(if i.val < 454 then
(if i.val < 453 then
60
else
62)
else
(if i.val < 455 then
66
else
67)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
68
else
1070)
else
(if i.val < 459 then
1071
else
1072))
else
(if i.val < 462 then
(if i.val < 461 then
1073
else
1074)
else
(if i.val < 463 then
1075
else
1076))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
1077
else
1078)
else
(if i.val < 467 then
1079
else
1080))
else
(if i.val < 470 then
(if i.val < 469 then
1081
else
1082)
else
(if i.val < 471 then
1083
else
1084)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
1085
else
1086)
else
(if i.val < 475 then
1087
else
1088))
else
(if i.val < 478 then
(if i.val < 477 then
1089
else
1090)
else
(if i.val < 479 then
1091
else
1290)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1291
else
536)
else
(if i.val < 483 then
1187
else
1218))
else
(if i.val < 486 then
(if i.val < 485 then
1292
else
1138)
else
(if i.val < 487 then
1127
else
1139)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
1175
else
1188)
else
(if i.val < 491 then
1219
else
1220))
else
(if i.val < 494 then
(if i.val < 493 then
1221
else
1293)
else
(if i.val < 495 then
1294
else
1295))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
1296
else
1297)
else
(if i.val < 499 then
1298
else
1299))
else
(if i.val < 502 then
(if i.val < 501 then
1300
else
1194)
else
(if i.val < 503 then
1301
else
1302)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
1223
else
1190)
else
(if i.val < 507 then
1225
else
1195))
else
(if i.val < 510 then
(if i.val < 509 then
1196
else
1303)
else
(if i.val < 511 then
1304
else
1305)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0001 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
1306
else
1307)
else
(if i.val < 515 then
1308
else
1309))
else
(if i.val < 518 then
(if i.val < 517 then
1310
else
1222)
else
(if i.val < 519 then
1224
else
70)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
76
else
77)
else
(if i.val < 523 then
1226
else
1227))
else
(if i.val < 526 then
(if i.val < 525 then
1228
else
1189)
else
(if i.val < 527 then
73
else
920))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
1191
else
1192)
else
(if i.val < 531 then
1193
else
1229))
else
(if i.val < 534 then
(if i.val < 533 then
1230
else
1231)
else
(if i.val < 535 then
1232
else
1233)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
1234
else
1235)
else
(if i.val < 539 then
1311
else
1312))
else
(if i.val < 542 then
(if i.val < 541 then
1313
else
1314)
else
(if i.val < 543 then
1315
else
1316)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
1317
else
1318)
else
(if i.val < 547 then
1319
else
1320))
else
(if i.val < 550 then
(if i.val < 549 then
1321
else
1322)
else
(if i.val < 551 then
1323
else
1324)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
1325
else
1326)
else
(if i.val < 555 then
1327
else
1328))
else
(if i.val < 558 then
(if i.val < 557 then
1238
else
1329)
else
(if i.val < 559 then
1239
else
1330))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
1331
else
1332)
else
(if i.val < 563 then
1333
else
1334))
else
(if i.val < 566 then
(if i.val < 565 then
1335
else
1336)
else
(if i.val < 567 then
1337
else
1338)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1339
else
69)
else
(if i.val < 571 then
71
else
72))
else
(if i.val < 574 then
(if i.val < 573 then
74
else
78)
else
(if i.val < 575 then
79
else
80))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
89
else
90)
else
(if i.val < 579 then
91
else
92))
else
(if i.val < 582 then
(if i.val < 581 then
93
else
94)
else
(if i.val < 583 then
95
else
1340)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
1341
else
1342)
else
(if i.val < 587 then
1343
else
1344))
else
(if i.val < 590 then
(if i.val < 589 then
1345
else
1346)
else
(if i.val < 591 then
1347
else
1348))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1349
else
1350)
else
(if i.val < 595 then
1351
else
1352))
else
(if i.val < 598 then
(if i.val < 597 then
1353
else
1354)
else
(if i.val < 599 then
647
else
615)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
1355
else
1356)
else
(if i.val < 603 then
1357
else
1358))
else
(if i.val < 606 then
(if i.val < 605 then
1359
else
1360)
else
(if i.val < 607 then
1361
else
1362)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
1363
else
1364)
else
(if i.val < 611 then
1365
else
1366))
else
(if i.val < 614 then
(if i.val < 613 then
1367
else
1368)
else
(if i.val < 615 then
1369
else
1370)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1371
else
1372)
else
(if i.val < 619 then
676
else
1373))
else
(if i.val < 622 then
(if i.val < 621 then
1374
else
1375)
else
(if i.val < 623 then
1376
else
1377))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
1378
else
1379)
else
(if i.val < 627 then
1380
else
1381))
else
(if i.val < 630 then
(if i.val < 629 then
1382
else
1685)
else
(if i.val < 631 then
1844
else
1845)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
1846
else
664)
else
(if i.val < 635 then
1469
else
1686))
else
(if i.val < 638 then
(if i.val < 637 then
715
else
1613)
else
(if i.val < 639 then
1504
else
1687)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
660
else
1488)
else
(if i.val < 643 then
1847
else
1848))
else
(if i.val < 646 then
(if i.val < 645 then
1849
else
98)
else
(if i.val < 647 then
1497
else
1467)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
1456
else
1468)
else
(if i.val < 651 then
1498
else
1499))
else
(if i.val < 654 then
(if i.val < 653 then
1500
else
1580)
else
(if i.val < 655 then
1569
else
1581))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
1614
else
1615)
else
(if i.val < 659 then
1616
else
1688))
else
(if i.val < 662 then
(if i.val < 661 then
1689
else
1690)
else
(if i.val < 663 then
1691
else
1692)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
266
else
1693)
else
(if i.val < 667 then
927
else
1679))
else
(if i.val < 670 then
(if i.val < 669 then
1850
else
1851)
else
(if i.val < 671 then
1852
else
1853)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
1854
else
1855)
else
(if i.val < 675 then
1856
else
1857))
else
(if i.val < 678 then
(if i.val < 677 then
1741
else
1858)
else
(if i.val < 679 then
1859
else
1860)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
1629
else
1861)
else
(if i.val < 683 then
1862
else
1695))
else
(if i.val < 686 then
(if i.val < 685 then
1863
else
1864)
else
(if i.val < 687 then
1588
else
1630))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
1865
else
1866)
else
(if i.val < 691 then
1867
else
1868))
else
(if i.val < 694 then
(if i.val < 693 then
1869
else
1870)
else
(if i.val < 695 then
1871
else
1872)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1694
else
1696)
else
(if i.val < 699 then
950
else
116))
else
(if i.val < 702 then
(if i.val < 701 then
1619
else
1699)
else
(if i.val < 703 then
1700
else
1701))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
1631
else
108)
else
(if i.val < 707 then
1632
else
1633))
else
(if i.val < 710 then
(if i.val < 709 then
1634
else
1635)
else
(if i.val < 711 then
1873
else
1874)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
1875
else
1876)
else
(if i.val < 715 then
1877
else
1878))
else
(if i.val < 718 then
(if i.val < 717 then
1879
else
605)
else
(if i.val < 719 then
1880
else
1881))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
1882
else
1883)
else
(if i.val < 723 then
1884
else
1885))
else
(if i.val < 726 then
(if i.val < 725 then
1886
else
1887)
else
(if i.val < 727 then
1888
else
1889)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
1890
else
440)
else
(if i.val < 731 then
763
else
1472))
else
(if i.val < 734 then
(if i.val < 733 then
1697
else
1698)
else
(if i.val < 735 then
96
else
99)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
100
else
117)
else
(if i.val < 739 then
118
else
119))
else
(if i.val < 742 then
(if i.val < 741 then
120
else
1702)
else
(if i.val < 743 then
1703
else
1704)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
1705
else
1706)
else
(if i.val < 747 then
261
else
1707))
else
(if i.val < 750 then
(if i.val < 749 then
1617
else
1618)
else
(if i.val < 751 then
105
else
109))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
1620
else
1621)
else
(if i.val < 755 then
1622
else
1623))
else
(if i.val < 758 then
(if i.val < 757 then
1624
else
1625)
else
(if i.val < 759 then
1626
else
1627)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
1628
else
1281)
else
(if i.val < 763 then
1708
else
263))
else
(if i.val < 766 then
(if i.val < 765 then
1709
else
1710)
else
(if i.val < 767 then
1711
else
1712))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
1713
else
1714)
else
(if i.val < 771 then
1715
else
1716))
else
(if i.val < 774 then
(if i.val < 773 then
1717
else
1718)
else
(if i.val < 775 then
1719
else
914)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1720
else
1721)
else
(if i.val < 779 then
1891
else
1892))
else
(if i.val < 782 then
(if i.val < 781 then
1893
else
1894)
else
(if i.val < 783 then
1895
else
1798))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1896
else
1897)
else
(if i.val < 787 then
1898
else
1899))
else
(if i.val < 790 then
(if i.val < 789 then
1900
else
1810)
else
(if i.val < 791 then
1901
else
1902)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
1903
else
1904)
else
(if i.val < 795 then
324
else
1905))
else
(if i.val < 798 then
(if i.val < 797 then
1906
else
1907)
else
(if i.val < 799 then
1908
else
1909)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1910
else
1911)
else
(if i.val < 803 then
1912
else
1913))
else
(if i.val < 806 then
(if i.val < 805 then
1914
else
1915)
else
(if i.val < 807 then
1916
else
1917)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
1918
else
1919)
else
(if i.val < 811 then
1920
else
1921))
else
(if i.val < 814 then
(if i.val < 813 then
1922
else
1923)
else
(if i.val < 815 then
1924
else
1726))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
1513
else
1727)
else
(if i.val < 819 then
1925
else
1926))
else
(if i.val < 822 then
(if i.val < 821 then
1728
else
1729)
else
(if i.val < 823 then
1730
else
1927)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
1928
else
1929)
else
(if i.val < 827 then
1930
else
1931))
else
(if i.val < 830 then
(if i.val < 829 then
1932
else
1933)
else
(if i.val < 831 then
1934
else
1935))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
1936
else
794)
else
(if i.val < 835 then
1937
else
1938))
else
(if i.val < 838 then
(if i.val < 837 then
1939
else
1940)
else
(if i.val < 839 then
1941
else
1942)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
1943
else
1944)
else
(if i.val < 843 then
1945
else
1946))
else
(if i.val < 846 then
(if i.val < 845 then
97
else
101)
else
(if i.val < 847 then
102
else
103))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
104
else
106)
else
(if i.val < 851 then
110
else
111))
else
(if i.val < 854 then
(if i.val < 853 then
112
else
121)
else
(if i.val < 855 then
122
else
123)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
124
else
125)
else
(if i.val < 859 then
126
else
127))
else
(if i.val < 862 then
(if i.val < 861 then
149
else
150)
else
(if i.val < 863 then
151
else
152)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
153
else
154)
else
(if i.val < 867 then
155
else
156))
else
(if i.val < 870 then
(if i.val < 869 then
157
else
158)
else
(if i.val < 871 then
159
else
160)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
161
else
162)
else
(if i.val < 875 then
163
else
164))
else
(if i.val < 878 then
(if i.val < 877 then
1947
else
1948)
else
(if i.val < 879 then
946
else
1949))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1950
else
1951)
else
(if i.val < 883 then
1952
else
1953))
else
(if i.val < 886 then
(if i.val < 885 then
1954
else
1955)
else
(if i.val < 887 then
933
else
1956)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1957
else
1958)
else
(if i.val < 891 then
1959
else
1960))
else
(if i.val < 894 then
(if i.val < 893 then
384
else
1961)
else
(if i.val < 895 then
1962
else
1963)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
1964
else
1965)
else
(if i.val < 899 then
1966
else
1967))
else
(if i.val < 902 then
(if i.val < 901 then
1530
else
1968)
else
(if i.val < 903 then
1969
else
1970)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
1971
else
1972)
else
(if i.val < 907 then
1973
else
1974))
else
(if i.val < 910 then
(if i.val < 909 then
1975
else
1976)
else
(if i.val < 911 then
1162
else
1977))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
1978
else
948)
else
(if i.val < 915 then
977
else
1979))
else
(if i.val < 918 then
(if i.val < 917 then
1124
else
484)
else
(if i.val < 919 then
1980
else
1981)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1982
else
1983)
else
(if i.val < 923 then
1984
else
1985))
else
(if i.val < 926 then
(if i.val < 925 then
1986
else
1987)
else
(if i.val < 927 then
1988
else
1989)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
1990
else
1991)
else
(if i.val < 931 then
1992
else
1993))
else
(if i.val < 934 then
(if i.val < 933 then
1994
else
394)
else
(if i.val < 935 then
1995
else
1996)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1997
else
1998)
else
(if i.val < 939 then
1999
else
2000))
else
(if i.val < 942 then
(if i.val < 941 then
2001
else
2002)
else
(if i.val < 943 then
2003
else
2004))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
2005
else
2006)
else
(if i.val < 947 then
386
else
2007))
else
(if i.val < 950 then
(if i.val < 949 then
2008
else
2009)
else
(if i.val < 951 then
307
else
2010)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
2011
else
2012)
else
(if i.val < 955 then
2013
else
2014))
else
(if i.val < 958 then
(if i.val < 957 then
2015
else
2016)
else
(if i.val < 959 then
2017
else
2018))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
2019
else
2020)
else
(if i.val < 963 then
2021
else
2022))
else
(if i.val < 966 then
(if i.val < 965 then
2023
else
2024)
else
(if i.val < 967 then
2025
else
2026)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
2027
else
2028)
else
(if i.val < 971 then
2029
else
2030))
else
(if i.val < 974 then
(if i.val < 973 then
2031
else
2032)
else
(if i.val < 975 then
2033
else
2034))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
2035
else
775)
else
(if i.val < 979 then
654
else
2036))
else
(if i.val < 982 then
(if i.val < 981 then
2037
else
2330)
else
(if i.val < 983 then
1034
else
2242)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
2268
else
2331)
else
(if i.val < 987 then
2199
else
2189))
else
(if i.val < 990 then
(if i.val < 989 then
2200
else
2230)
else
(if i.val < 991 then
2243
else
2269)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
2270
else
2271)
else
(if i.val < 995 then
2332
else
2333))
else
(if i.val < 998 then
(if i.val < 997 then
2334
else
2335)
else
(if i.val < 999 then
1747
else
2336)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
2337
else
2248)
else
(if i.val < 1003 then
1816
else
2338))
else
(if i.val < 1006 then
(if i.val < 1005 then
2273
else
2245)
else
(if i.val < 1007 then
2275
else
2249))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
2250
else
2339)
else
(if i.val < 1011 then
2340
else
2341))
else
(if i.val < 1014 then
(if i.val < 1013 then
2342
else
2343)
else
(if i.val < 1015 then
2344
else
2345)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
2272
else
2274)
else
(if i.val < 1019 then
166
else
172))
else
(if i.val < 1022 then
(if i.val < 1021 then
173
else
2276)
else
(if i.val < 1023 then
2277
else
2278)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0002 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
2244
else
169)
else
(if i.val < 1027 then
1396
else
2246))
else
(if i.val < 1030 then
(if i.val < 1029 then
2247
else
2279)
else
(if i.val < 1031 then
2280
else
2281)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
2282
else
2283)
else
(if i.val < 1035 then
2284
else
2285))
else
(if i.val < 1038 then
(if i.val < 1037 then
2346
else
2347)
else
(if i.val < 1039 then
2348
else
2349))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
2350
else
2351)
else
(if i.val < 1043 then
2352
else
796))
else
(if i.val < 1046 then
(if i.val < 1045 then
2353
else
2354)
else
(if i.val < 1047 then
2355
else
2356)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
2357
else
2358)
else
(if i.val < 1051 then
2359
else
2288))
else
(if i.val < 1054 then
(if i.val < 1053 then
2360
else
2289)
else
(if i.val < 1055 then
2361
else
2362)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
2363
else
2364)
else
(if i.val < 1059 then
2365
else
2366))
else
(if i.val < 1062 then
(if i.val < 1061 then
729
else
2367)
else
(if i.val < 1063 then
2368
else
165)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
167
else
168)
else
(if i.val < 1067 then
170
else
174))
else
(if i.val < 1070 then
(if i.val < 1069 then
175
else
176)
else
(if i.val < 1071 then
185
else
186))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
187
else
188)
else
(if i.val < 1075 then
189
else
190))
else
(if i.val < 1078 then
(if i.val < 1077 then
191
else
2369)
else
(if i.val < 1079 then
2370
else
1824)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
2371
else
2372)
else
(if i.val < 1083 then
2373
else
2374))
else
(if i.val < 1086 then
(if i.val < 1085 then
2375
else
2376)
else
(if i.val < 1087 then
2377
else
2378))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
2379
else
2380)
else
(if i.val < 1091 then
2381
else
2382))
else
(if i.val < 1094 then
(if i.val < 1093 then
1140
else
1109)
else
(if i.val < 1095 then
2383
else
2384)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
2385
else
2126)
else
(if i.val < 1099 then
2386
else
2387))
else
(if i.val < 1102 then
(if i.val < 1101 then
2388
else
2389)
else
(if i.val < 1103 then
2390
else
2391))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
2392
else
2393)
else
(if i.val < 1107 then
682
else
2394))
else
(if i.val < 1110 then
(if i.val < 1109 then
2395
else
2396)
else
(if i.val < 1111 then
2397
else
2398)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
1169
else
2399)
else
(if i.val < 1115 then
2400
else
2401))
else
(if i.val < 1118 then
(if i.val < 1117 then
2402
else
2403)
else
(if i.val < 1119 then
2404
else
2405)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
2406
else
2407)
else
(if i.val < 1123 then
2408
else
2678))
else
(if i.val < 1126 then
(if i.val < 1125 then
2813
else
2814)
else
(if i.val < 1127 then
2815
else
1157)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
2489
else
2679)
else
(if i.val < 1131 then
1205
else
2615))
else
(if i.val < 1134 then
(if i.val < 1133 then
2519
else
1153)
else
(if i.val < 1135 then
2504
else
2816))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
2817
else
2818)
else
(if i.val < 1139 then
194
else
2512))
else
(if i.val < 1142 then
(if i.val < 1141 then
2487
else
2476)
else
(if i.val < 1143 then
2488
else
2513)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
2514
else
2515)
else
(if i.val < 1147 then
2586
else
2580))
else
(if i.val < 1150 then
(if i.val < 1149 then
2075
else
2616)
else
(if i.val < 1151 then
2617
else
2618)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
2680
else
2681)
else
(if i.val < 1155 then
2682
else
2138))
else
(if i.val < 1158 then
(if i.val < 1157 then
2683
else
486)
else
(if i.val < 1159 then
2684
else
1403)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
2673
else
2819)
else
(if i.val < 1163 then
2820
else
2821))
else
(if i.val < 1166 then
(if i.val < 1165 then
2822
else
2823)
else
(if i.val < 1167 then
2824
else
2825))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
2826
else
2729)
else
(if i.val < 1171 then
2827
else
2828))
else
(if i.val < 1174 then
(if i.val < 1173 then
2829
else
2628)
else
(if i.val < 1175 then
2830
else
2686)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
2831
else
2832)
else
(if i.val < 1179 then
2591
else
2629))
else
(if i.val < 1182 then
(if i.val < 1181 then
2833
else
2834)
else
(if i.val < 1183 then
2835
else
2836)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
2837
else
2838)
else
(if i.val < 1187 then
2839
else
2685))
else
(if i.val < 1190 then
(if i.val < 1189 then
2687
else
1426)
else
(if i.val < 1191 then
211
else
2690)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
2691
else
2692)
else
(if i.val < 1195 then
2630
else
203))
else
(if i.val < 1198 then
(if i.val < 1197 then
2068
else
2631)
else
(if i.val < 1199 then
2632
else
2633))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
2840
else
2841)
else
(if i.val < 1203 then
2842
else
2843))
else
(if i.val < 1206 then
(if i.val < 1205 then
714
else
2844)
else
(if i.val < 1207 then
2845
else
1099)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
2846
else
2847)
else
(if i.val < 1211 then
2848
else
2849))
else
(if i.val < 1214 then
(if i.val < 1213 then
2850
else
2851)
else
(if i.val < 1215 then
2852
else
2853))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
2854
else
2855)
else
(if i.val < 1219 then
1251
else
2492))
else
(if i.val < 1222 then
(if i.val < 1221 then
2688
else
2689)
else
(if i.val < 1223 then
192
else
195)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
196
else
212)
else
(if i.val < 1227 then
213
else
214))
else
(if i.val < 1230 then
(if i.val < 1229 then
215
else
2693)
else
(if i.val < 1231 then
2694
else
2695))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
2696
else
2697)
else
(if i.val < 1235 then
481
else
2698))
else
(if i.val < 1238 then
(if i.val < 1237 then
2619
else
2067)
else
(if i.val < 1239 then
200
else
204)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
2620
else
2621)
else
(if i.val < 1243 then
2622
else
2623))
else
(if i.val < 1246 then
(if i.val < 1245 then
2152
else
2624)
else
(if i.val < 1247 then
2625
else
2626)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
2627
else
2322)
else
(if i.val < 1251 then
2054
else
483))
else
(if i.val < 1254 then
(if i.val < 1253 then
2699
else
2700)
else
(if i.val < 1255 then
2701
else
2702)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
2703
else
2704)
else
(if i.val < 1259 then
2705
else
2706))
else
(if i.val < 1262 then
(if i.val < 1261 then
2707
else
2708)
else
(if i.val < 1263 then
1390
else
2709))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
2710
else
2856)
else
(if i.val < 1267 then
2857
else
2858))
else
(if i.val < 1270 then
(if i.val < 1269 then
2859
else
2774)
else
(if i.val < 1271 then
2860
else
2861)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
2862
else
2863)
else
(if i.val < 1275 then
2864
else
2785))
else
(if i.val < 1278 then
(if i.val < 1277 then
790
else
2865)
else
(if i.val < 1279 then
2866
else
542))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
2867
else
2868)
else
(if i.val < 1283 then
2869
else
2870))
else
(if i.val < 1286 then
(if i.val < 1285 then
2871
else
2872)
else
(if i.val < 1287 then
2873
else
2874)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
2875
else
2876)
else
(if i.val < 1291 then
1558
else
2877))
else
(if i.val < 1294 then
(if i.val < 1293 then
917
else
2878)
else
(if i.val < 1295 then
2879
else
2880))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
2881
else
2882)
else
(if i.val < 1299 then
2883
else
2715))
else
(if i.val < 1302 then
(if i.val < 1301 then
2528
else
2716)
else
(if i.val < 1303 then
2884
else
2717)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
2718
else
2719)
else
(if i.val < 1307 then
2885
else
2886))
else
(if i.val < 1310 then
(if i.val < 1309 then
2887
else
2888)
else
(if i.val < 1311 then
1652
else
2889)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
2890
else
2891)
else
(if i.val < 1315 then
2892
else
1279))
else
(if i.val < 1318 then
(if i.val < 1317 then
2893
else
2894)
else
(if i.val < 1319 then
2895
else
2896)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
2897
else
2898)
else
(if i.val < 1323 then
2899
else
2900))
else
(if i.val < 1326 then
(if i.val < 1325 then
2901
else
193)
else
(if i.val < 1327 then
197
else
198))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
199
else
201)
else
(if i.val < 1331 then
205
else
206))
else
(if i.val < 1334 then
(if i.val < 1333 then
207
else
216)
else
(if i.val < 1335 then
217
else
218)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
219
else
220)
else
(if i.val < 1339 then
221
else
222))
else
(if i.val < 1342 then
(if i.val < 1341 then
244
else
245)
else
(if i.val < 1343 then
246
else
247))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
248
else
249)
else
(if i.val < 1347 then
250
else
251))
else
(if i.val < 1350 then
(if i.val < 1349 then
252
else
253)
else
(if i.val < 1351 then
254
else
255)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
256
else
257)
else
(if i.val < 1355 then
258
else
2902))
else
(if i.val < 1358 then
(if i.val < 1357 then
1422
else
2903)
else
(if i.val < 1359 then
2904
else
2905))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
717
else
2906)
else
(if i.val < 1363 then
2907
else
2908))
else
(if i.val < 1366 then
(if i.val < 1365 then
1409
else
2909)
else
(if i.val < 1367 then
2910
else
2911)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
2912
else
2913)
else
(if i.val < 1371 then
599
else
2914))
else
(if i.val < 1374 then
(if i.val < 1373 then
2915
else
2916)
else
(if i.val < 1375 then
2917
else
2918)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
2919
else
2545)
else
(if i.val < 1379 then
2920
else
2921))
else
(if i.val < 1382 then
(if i.val < 1381 then
2922
else
2923)
else
(if i.val < 1383 then
2924
else
2925)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
2926
else
1582)
else
(if i.val < 1387 then
2220
else
2927))
else
(if i.val < 1390 then
(if i.val < 1389 then
2928
else
1424)
else
(if i.val < 1391 then
1452
else
2929))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
2186
else
985)
else
(if i.val < 1395 then
2930
else
1503))
else
(if i.val < 1398 then
(if i.val < 1397 then
2931
else
2932)
else
(if i.val < 1399 then
2933
else
2934)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
2935
else
1466)
else
(if i.val < 1403 then
2936
else
2937))
else
(if i.val < 1406 then
(if i.val < 1405 then
2938
else
2939)
else
(if i.val < 1407 then
2940
else
2941)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
2942
else
609)
else
(if i.val < 1411 then
2943
else
2944))
else
(if i.val < 1414 then
(if i.val < 1413 then
2945
else
2946)
else
(if i.val < 1415 then
2947
else
1610)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
1566
else
2948)
else
(if i.val < 1419 then
2949
else
2950))
else
(if i.val < 1422 then
(if i.val < 1421 then
2951
else
2952)
else
(if i.val < 1423 then
601
else
2953))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
2954
else
2955)
else
(if i.val < 1427 then
525
else
2956))
else
(if i.val < 1430 then
(if i.val < 1429 then
2957
else
2958)
else
(if i.val < 1431 then
2959
else
2960)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
2961
else
2962)
else
(if i.val < 1435 then
922
else
2963))
else
(if i.val < 1438 then
(if i.val < 1437 then
2964
else
2965)
else
(if i.val < 1439 then
2966
else
2967)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
2968
else
2969)
else
(if i.val < 1443 then
967
else
2970))
else
(if i.val < 1446 then
(if i.val < 1445 then
2971
else
2972)
else
(if i.val < 1447 then
2973
else
2974)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
2975
else
2976)
else
(if i.val < 1451 then
2977
else
2978))
else
(if i.val < 1454 then
(if i.val < 1453 then
1262
else
1147)
else
(if i.val < 1455 then
2979
else
1564))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
3188
else
3399)
else
(if i.val < 1459 then
3527
else
3777))
else
(if i.val < 1462 then
(if i.val < 1461 then
3778
else
3779)
else
(if i.val < 1463 then
3672
else
3780)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
3781
else
777)
else
(if i.val < 1467 then
3782
else
598))
else
(if i.val < 1470 then
(if i.val < 1469 then
3189
else
1511)
else
(if i.val < 1471 then
3135
else
3136))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
270
else
3528)
else
(if i.val < 1475 then
1508
else
1599))
else
(if i.val < 1478 then
(if i.val < 1477 then
3400
else
2421)
else
(if i.val < 1479 then
2430
else
1595)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
764
else
652)
else
(if i.val < 1483 then
3336
else
3529))
else
(if i.val < 1486 then
(if i.val < 1485 then
3530
else
3531)
else
(if i.val < 1487 then
3173
else
3783))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
3174
else
3170)
else
(if i.val < 1491 then
2434
else
2448))
else
(if i.val < 1494 then
(if i.val < 1493 then
3784
else
3785)
else
(if i.val < 1495 then
3182
else
3786)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
3787
else
267)
else
(if i.val < 1499 then
2772
else
2782))
else
(if i.val < 1502 then
(if i.val < 1501 then
1481
else
3105)
else
(if i.val < 1503 then
773
else
3106)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
3132
else
3133)
else
(if i.val < 1507 then
3134
else
3190))
else
(if i.val < 1510 then
(if i.val < 1509 then
3191
else
3192)
else
(if i.val < 1511 then
3193
else
634)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
3194
else
280)
else
(if i.val < 1515 then
3342
else
3319))
else
(if i.val < 1518 then
(if i.val < 1517 then
2461
else
3343)
else
(if i.val < 1519 then
3344
else
3345))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
3401
else
3402)
else
(if i.val < 1523 then
3403
else
3404))
else
(if i.val < 1526 then
(if i.val < 1525 then
3405
else
684)
else
(if i.val < 1527 then
3406
else
1802)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
635
else
1507)
else
(if i.val < 1531 then
408
else
3532))
else
(if i.val < 1534 then
(if i.val < 1533 then
3533
else
3534)
else
(if i.val < 1535 then
3535
else
3536)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0003 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
3537
else
3538)
else
(if i.val < 1539 then
3443
else
3539))
else
(if i.val < 1542 then
(if i.val < 1541 then
3540
else
3788)
else
(if i.val < 1543 then
3789
else
3790)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
2086
else
3791)
else
(if i.val < 1547 then
3792
else
3793))
else
(if i.val < 1550 then
(if i.val < 1549 then
762
else
3794)
else
(if i.val < 1551 then
3795
else
3796))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
3797
else
3798)
else
(if i.val < 1555 then
3799
else
3800))
else
(if i.val < 1558 then
(if i.val < 1557 then
3801
else
3802)
else
(if i.val < 1559 then
479
else
3803)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
3804
else
2651)
else
(if i.val < 1563 then
3805
else
3806))
else
(if i.val < 1566 then
(if i.val < 1565 then
3807
else
2759)
else
(if i.val < 1567 then
3808
else
3809)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
3810
else
978)
else
(if i.val < 1571 then
1672
else
3811))
else
(if i.val < 1574 then
(if i.val < 1573 then
1641
else
3427)
else
(if i.val < 1575 then
3812
else
3813)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
3814
else
3151)
else
(if i.val < 1579 then
3815
else
3816))
else
(if i.val < 1582 then
(if i.val < 1581 then
3407
else
3543)
else
(if i.val < 1583 then
2120
else
3817))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
3818
else
3819)
else
(if i.val < 1587 then
3820
else
3821))
else
(if i.val < 1590 then
(if i.val < 1589 then
3353
else
3324)
else
(if i.val < 1591 then
3354
else
3428)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
3429
else
3430)
else
(if i.val < 1595 then
3822
else
3823))
else
(if i.val < 1598 then
(if i.val < 1597 then
3824
else
3825)
else
(if i.val < 1599 then
1247
else
1842))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
3826
else
3827)
else
(if i.val < 1603 then
3469
else
3828))
else
(if i.val < 1606 then
(if i.val < 1605 then
3829
else
3830)
else
(if i.val < 1607 then
3831
else
3832)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
3391
else
3833)
else
(if i.val < 1611 then
3601
else
2754))
else
(if i.val < 1614 then
(if i.val < 1613 then
3239
else
3541)
else
(if i.val < 1615 then
3544
else
3545))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
2122
else
2121)
else
(if i.val < 1619 then
3408
else
309))
else
(if i.val < 1622 then
(if i.val < 1621 then
2125
else
3411)
else
(if i.val < 1623 then
3412
else
3549)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
3550
else
3551)
else
(if i.val < 1627 then
3552
else
3553))
else
(if i.val < 1630 then
(if i.val < 1629 then
3554
else
3431)
else
(if i.val < 1631 then
3432
else
281)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
289
else
3433)
else
(if i.val < 1635 then
3434
else
3435))
else
(if i.val < 1638 then
(if i.val < 1637 then
3436
else
3437)
else
(if i.val < 1639 then
3438
else
3022)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
2056
else
2137)
else
(if i.val < 1643 then
3439
else
3834))
else
(if i.val < 1646 then
(if i.val < 1645 then
3835
else
3836)
else
(if i.val < 1647 then
3837
else
3838))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
2049
else
3839)
else
(if i.val < 1651 then
3840
else
3841))
else
(if i.val < 1654 then
(if i.val < 1653 then
516
else
3842)
else
(if i.val < 1655 then
3843
else
3844)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
1246
else
2811)
else
(if i.val < 1659 then
3620
else
3845))
else
(if i.val < 1662 then
(if i.val < 1661 then
1404
else
3846)
else
(if i.val < 1663 then
3847
else
3848)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
3849
else
3850)
else
(if i.val < 1667 then
3851
else
805))
else
(if i.val < 1670 then
(if i.val < 1669 then
3671
else
3852)
else
(if i.val < 1671 then
3853
else
801)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
3225
else
3854)
else
(if i.val < 1675 then
3855
else
3856))
else
(if i.val < 1678 then
(if i.val < 1677 then
3857
else
2267)
else
(if i.val < 1679 then
3858
else
3859))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
1768
else
3860)
else
(if i.val < 1683 then
727
else
2675))
else
(if i.val < 1686 then
(if i.val < 1685 then
1762
else
3195)
else
(if i.val < 1687 then
1528
else
3542)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
2983
else
640)
else
(if i.val < 1691 then
3546
else
3547))
else
(if i.val < 1694 then
(if i.val < 1693 then
2995
else
3548)
else
(if i.val < 1695 then
262
else
268)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
269
else
271)
else
(if i.val < 1699 then
272
else
310))
else
(if i.val < 1702 then
(if i.val < 1701 then
311
else
312)
else
(if i.val < 1703 then
313
else
314)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
315
else
316)
else
(if i.val < 1707 then
317
else
319))
else
(if i.val < 1710 then
(if i.val < 1709 then
1548
else
1480)
else
(if i.val < 1711 then
3555
else
3556))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
3557
else
3558)
else
(if i.val < 1715 then
3559
else
3560))
else
(if i.val < 1718 then
(if i.val < 1717 then
3561
else
3562)
else
(if i.val < 1719 then
1502
else
2986)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
3563
else
1465)
else
(if i.val < 1723 then
1644
else
3322))
else
(if i.val < 1726 then
(if i.val < 1725 then
3409
else
3410)
else
(if i.val < 1727 then
279
else
282))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
290
else
291)
else
(if i.val < 1731 then
292
else
3413))
else
(if i.val < 1734 then
(if i.val < 1733 then
3414
else
979)
else
(if i.val < 1735 then
3415
else
3416)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
679
else
3417)
else
(if i.val < 1739 then
3418
else
681))
else
(if i.val < 1742 then
(if i.val < 1741 then
2422
else
618)
else
(if i.val < 1743 then
955
else
2435))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
3419
else
3420)
else
(if i.val < 1747 then
3421
else
3422))
else
(if i.val < 1750 then
(if i.val < 1749 then
3423
else
3424)
else
(if i.val < 1751 then
1789
else
3425)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
3426
else
3564)
else
(if i.val < 1755 then
3565
else
3566))
else
(if i.val < 1758 then
(if i.val < 1757 then
3567
else
3487)
else
(if i.val < 1759 then
3568
else
3569)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
3570
else
3571)
else
(if i.val < 1763 then
3572
else
3498))
else
(if i.val < 1766 then
(if i.val < 1765 then
3224
else
3573)
else
(if i.val < 1767 then
3574
else
3141)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
3575
else
3576)
else
(if i.val < 1771 then
720
else
3577))
else
(if i.val < 1774 then
(if i.val < 1773 then
3578
else
3579)
else
(if i.val < 1775 then
2109
else
3580))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
3581
else
3582)
else
(if i.val < 1779 then
2058
else
3583))
else
(if i.val < 1782 then
(if i.val < 1781 then
3584
else
3679)
else
(if i.val < 1783 then
3005
else
3861)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
3862
else
2560)
else
(if i.val < 1787 then
3863
else
3019))
else
(if i.val < 1790 then
(if i.val < 1789 then
3689
else
3622)
else
(if i.val < 1791 then
3864
else
2479))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
1586
else
3865)
else
(if i.val < 1795 then
3866
else
3703))
else
(if i.val < 1798 then
(if i.val < 1797 then
2202
else
3276)
else
(if i.val < 1799 then
3704
else
3867)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
3868
else
3869)
else
(if i.val < 1803 then
3870
else
3871))
else
(if i.val < 1806 then
(if i.val < 1805 then
3872
else
3873)
else
(if i.val < 1807 then
2203
else
3767))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
937
else
3874)
else
(if i.val < 1811 then
3523
else
780))
else
(if i.val < 1814 then
(if i.val < 1813 then
795
else
3741)
else
(if i.val < 1815 then
2796
else
3875)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
3876
else
3877)
else
(if i.val < 1819 then
3878
else
3879))
else
(if i.val < 1822 then
(if i.val < 1821 then
3880
else
3881)
else
(if i.val < 1823 then
3882
else
797)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
466
else
1813)
else
(if i.val < 1827 then
3883
else
3884))
else
(if i.val < 1830 then
(if i.val < 1829 then
3510
else
3885)
else
(if i.val < 1831 then
3886
else
3887)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
3888
else
3889)
else
(if i.val < 1835 then
3890
else
3891))
else
(if i.val < 1838 then
(if i.val < 1837 then
3499
else
3892)
else
(if i.val < 1839 then
3893
else
3894))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
3895
else
3896)
else
(if i.val < 1843 then
1475
else
3897))
else
(if i.val < 1846 then
(if i.val < 1845 then
2418
else
3898)
else
(if i.val < 1847 then
3899
else
3331)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
3900
else
3901)
else
(if i.val < 1851 then
3902
else
2412))
else
(if i.val < 1854 then
(if i.val < 1853 then
3903
else
3904)
else
(if i.val < 1855 then
3905
else
3906))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
3907
else
3908)
else
(if i.val < 1859 then
3063
else
3375))
else
(if i.val < 1862 then
(if i.val < 1861 then
1736
else
1739)
else
(if i.val < 1863 then
1106
else
1525)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
3213
else
3146)
else
(if i.val < 1867 then
3593
else
3594))
else
(if i.val < 1870 then
(if i.val < 1869 then
3909
else
3910)
else
(if i.val < 1871 then
3911
else
3912))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
3913
else
3595)
else
(if i.val < 1875 then
3596
else
3597))
else
(if i.val < 1878 then
(if i.val < 1877 then
3598
else
1204)
else
(if i.val < 1879 then
636
else
2146)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
3373
else
3914)
else
(if i.val < 1883 then
1770
else
3915))
else
(if i.val < 1886 then
(if i.val < 1885 then
3916
else
3917)
else
(if i.val < 1887 then
2048
else
3918)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
3726
else
1682)
else
(if i.val < 1891 then
2671
else
3919))
else
(if i.val < 1894 then
(if i.val < 1893 then
3470
else
1811)
else
(if i.val < 1895 then
3920
else
3921)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
3922
else
3923)
else
(if i.val < 1899 then
3924
else
3925))
else
(if i.val < 1902 then
(if i.val < 1901 then
3926
else
1276)
else
(if i.val < 1903 then
3927
else
3928))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
3352
else
1812)
else
(if i.val < 1907 then
1043
else
1823))
else
(if i.val < 1910 then
(if i.val < 1909 then
3929
else
3930)
else
(if i.val < 1911 then
3230
else
1671)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
3931
else
3932)
else
(if i.val < 1915 then
3933
else
1667))
else
(if i.val < 1918 then
(if i.val < 1917 then
259
else
260)
else
(if i.val < 1919 then
264
else
273)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
274
else
275)
else
(if i.val < 1923 then
276
else
277))
else
(if i.val < 1926 then
(if i.val < 1925 then
278
else
283)
else
(if i.val < 1927 then
284
else
293)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
294
else
295)
else
(if i.val < 1931 then
296
else
297))
else
(if i.val < 1934 then
(if i.val < 1933 then
298
else
320)
else
(if i.val < 1935 then
321
else
322))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
323
else
325)
else
(if i.val < 1939 then
326
else
327))
else
(if i.val < 1942 then
(if i.val < 1941 then
328
else
329)
else
(if i.val < 1943 then
330
else
331)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
332
else
333)
else
(if i.val < 1947 then
334
else
383))
else
(if i.val < 1950 then
(if i.val < 1949 then
385
else
387)
else
(if i.val < 1951 then
388
else
389)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
390
else
391)
else
(if i.val < 1955 then
392
else
393))
else
(if i.val < 1958 then
(if i.val < 1957 then
395
else
396)
else
(if i.val < 1959 then
397
else
398)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
399
else
401)
else
(if i.val < 1963 then
402
else
403))
else
(if i.val < 1966 then
(if i.val < 1965 then
404
else
405)
else
(if i.val < 1967 then
406
else
407))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
409
else
410)
else
(if i.val < 1971 then
411
else
412))
else
(if i.val < 1974 then
(if i.val < 1973 then
413
else
3934)
else
(if i.val < 1975 then
3935
else
3936)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
3937
else
3938)
else
(if i.val < 1979 then
3939
else
3940))
else
(if i.val < 1982 then
(if i.val < 1981 then
3941
else
3942)
else
(if i.val < 1983 then
527
else
2496))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
1434
else
2728)
else
(if i.val < 1987 then
3943
else
3944))
else
(if i.val < 1990 then
(if i.val < 1989 then
3945
else
666)
else
(if i.val < 1991 then
3946
else
3947)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
3948
else
2497)
else
(if i.val < 1995 then
2050
else
3949))
else
(if i.val < 1998 then
(if i.val < 1997 then
3950
else
2506)
else
(if i.val < 1999 then
1808
else
2094))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
3670
else
3951)
else
(if i.val < 2003 then
3952
else
3953))
else
(if i.val < 2006 then
(if i.val < 2005 then
3954
else
3955)
else
(if i.val < 2007 then
3956
else
2158)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
913
else
2096)
else
(if i.val < 2011 then
2507
else
3957))
else
(if i.val < 2014 then
(if i.val < 2013 then
3958
else
3959)
else
(if i.val < 2015 then
1742
else
3960)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
3663
else
3961)
else
(if i.val < 2019 then
3962
else
3963))
else
(if i.val < 2022 then
(if i.val < 2021 then
3964
else
2133)
else
(if i.val < 2023 then
3965
else
2127)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
2531
else
3966)
else
(if i.val < 2027 then
1442
else
3967))
else
(if i.val < 2030 then
(if i.val < 2029 then
3968
else
3969)
else
(if i.val < 2031 then
2104
else
3646))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
3970
else
3971)
else
(if i.val < 2035 then
3972
else
3973))
else
(if i.val < 2038 then
(if i.val < 2037 then
1733
else
3974)
else
(if i.val < 2039 then
3975
else
3976)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
3977
else
2210)
else
(if i.val < 2043 then
2190
else
3978))
else
(if i.val < 2046 then
(if i.val < 2045 then
3979
else
3980)
else
(if i.val < 2047 then
3127
else
2306)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0004 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
724
else
3981)
else
(if i.val < 2051 then
932
else
2099))
else
(if i.val < 2054 then
(if i.val < 2053 then
3982
else
3983)
else
(if i.val < 2055 then
2561
else
1134)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
2214
else
3984)
else
(if i.val < 2059 then
2178
else
3985))
else
(if i.val < 2062 then
(if i.val < 2061 then
3486
else
1602)
else
(if i.val < 2063 then
3986
else
3987))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
3988
else
3989)
else
(if i.val < 2067 then
3990
else
3991))
else
(if i.val < 2070 then
(if i.val < 2069 then
508
else
2666)
else
(if i.val < 2071 then
3992
else
3993)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
3994
else
3995)
else
(if i.val < 2075 then
3996
else
3997))
else
(if i.val < 2078 then
(if i.val < 2077 then
3998
else
3999)
else
(if i.val < 2079 then
4000
else
4001)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
4002
else
4003)
else
(if i.val < 2083 then
4004
else
4005))
else
(if i.val < 2086 then
(if i.val < 2085 then
4006
else
4007)
else
(if i.val < 2087 then
4008
else
4009)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
4010
else
1554)
else
(if i.val < 2091 then
4011
else
4012))
else
(if i.val < 2094 then
(if i.val < 2093 then
4013
else
4014)
else
(if i.val < 2095 then
938
else
4015))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
949
else
4016)
else
(if i.val < 2099 then
4017
else
4018))
else
(if i.val < 2102 then
(if i.val < 2101 then
4019
else
4020)
else
(if i.val < 2103 then
4021
else
4022)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
971
else
4023)
else
(if i.val < 2107 then
4024
else
3450))
else
(if i.val < 2110 then
(if i.val < 2109 then
4025
else
2164)
else
(if i.val < 2111 then
4026
else
2052))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
4027
else
4028)
else
(if i.val < 2115 then
4029
else
2124))
else
(if i.val < 2118 then
(if i.val < 2117 then
3116
else
4030)
else
(if i.val < 2119 then
4031
else
3271)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
1385
else
748)
else
(if i.val < 2123 then
658
else
4032))
else
(if i.val < 2126 then
(if i.val < 2125 then
4033
else
752)
else
(if i.val < 2127 then
3511
else
964))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
4034
else
4035)
else
(if i.val < 2131 then
2226
else
4036))
else
(if i.val < 2134 then
(if i.val < 2133 then
4037
else
962)
else
(if i.val < 2135 then
3126
else
4038)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
4039
else
1572)
else
(if i.val < 2139 then
4040
else
2176))
else
(if i.val < 2142 then
(if i.val < 2141 then
4041
else
4042)
else
(if i.val < 2143 then
4043
else
2301)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
1397
else
1796)
else
(if i.val < 2147 then
716
else
1779))
else
(if i.val < 2150 then
(if i.val < 2149 then
4044
else
2184)
else
(if i.val < 2151 then
4045
else
4046)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
4047
else
3054)
else
(if i.val < 2155 then
1428
else
4048))
else
(if i.val < 2158 then
(if i.val < 2157 then
4049
else
4050)
else
(if i.val < 2159 then
947
else
3668))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
4051
else
4052)
else
(if i.val < 2163 then
4053
else
4054))
else
(if i.val < 2166 then
(if i.val < 2165 then
1774
else
1535)
else
(if i.val < 2167 then
4055
else
4056)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
4057
else
4058)
else
(if i.val < 2171 then
4059
else
4060))
else
(if i.val < 2174 then
(if i.val < 2173 then
4061
else
4062)
else
(if i.val < 2175 then
1655
else
4063)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
4064
else
2072)
else
(if i.val < 2179 then
1778
else
1776))
else
(if i.val < 2182 then
(if i.val < 2181 then
4065
else
1740)
else
(if i.val < 2183 then
4066
else
4067)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
4068
else
4424)
else
(if i.val < 2187 then
4513
else
4514))
else
(if i.val < 2190 then
(if i.val < 2189 then
4515
else
2215)
else
(if i.val < 2191 then
3756
else
4078))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
2257
else
4383)
else
(if i.val < 2195 then
2211
else
4309))
else
(if i.val < 2198 then
(if i.val < 2197 then
4516
else
3248)
else
(if i.val < 2199 then
4517
else
415)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
4316
else
4291)
else
(if i.val < 2203 then
2145
else
4317))
else
(if i.val < 2206 then
(if i.val < 2205 then
4363
else
4357)
else
(if i.val < 2207 then
3014
else
4384)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
4385
else
4386)
else
(if i.val < 2211 then
4425
else
4426))
else
(if i.val < 2214 then
(if i.val < 2213 then
3619
else
3071)
else
(if i.val < 2215 then
1640
else
987)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
3237
else
2426)
else
(if i.val < 2219 then
4421
else
4518))
else
(if i.val < 2222 then
(if i.val < 2221 then
4519
else
4520)
else
(if i.val < 2223 then
4521
else
4522))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
4523
else
4524)
else
(if i.val < 2227 then
3615
else
4525))
else
(if i.val < 2230 then
(if i.val < 2229 then
4395
else
4526)
else
(if i.val < 2231 then
4428
else
4527)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
4528
else
4366)
else
(if i.val < 2235 then
3723
else
3729))
else
(if i.val < 2238 then
(if i.val < 2237 then
3694
else
3733)
else
(if i.val < 2239 then
4529
else
4530))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
4531
else
4532)
else
(if i.val < 2243 then
4427
else
3293))
else
(if i.val < 2246 then
(if i.val < 2245 then
2447
else
432)
else
(if i.val < 2247 then
4431
else
4432)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
4396
else
424)
else
(if i.val < 2251 then
3007
else
4397))
else
(if i.val < 2254 then
(if i.val < 2253 then
4398
else
4533)
else
(if i.val < 2255 then
4534
else
4535))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
4536
else
4537)
else
(if i.val < 2259 then
4538
else
4539))
else
(if i.val < 2262 then
(if i.val < 2261 then
4540
else
4541)
else
(if i.val < 2263 then
2084
else
4542)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
4543
else
4544)
else
(if i.val < 2267 then
3453
else
3520))
else
(if i.val < 2270 then
(if i.val < 2269 then
2300
else
4301)
else
(if i.val < 2271 then
4429
else
4430)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
414
else
416)
else
(if i.val < 2275 then
417
else
433))
else
(if i.val < 2278 then
(if i.val < 2277 then
434
else
435)
else
(if i.val < 2279 then
436
else
4224)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
4433
else
4434)
else
(if i.val < 2283 then
4435
else
4436))
else
(if i.val < 2286 then
(if i.val < 2285 then
982
else
4437)
else
(if i.val < 2287 then
4387
else
3006))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
421
else
425)
else
(if i.val < 2291 then
4388
else
4389))
else
(if i.val < 2294 then
(if i.val < 2293 then
4390
else
4391)
else
(if i.val < 2295 then
3079
else
4392)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
4142
else
4393)
else
(if i.val < 2299 then
4394
else
2993))
else
(if i.val < 2302 then
(if i.val < 2301 then
984
else
4438)
else
(if i.val < 2303 then
4439
else
4440))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
1560
else
4235)
else
(if i.val < 2307 then
4441
else
2416))
else
(if i.val < 2310 then
(if i.val < 2309 then
4442
else
4443)
else
(if i.val < 2311 then
4545
else
3621)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
4546
else
4487)
else
(if i.val < 2315 then
4547
else
4548))
else
(if i.val < 2318 then
(if i.val < 2317 then
4549
else
4550)
else
(if i.val < 2319 then
4495
else
4551))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
4552
else
1040)
else
(if i.val < 2323 then
4553
else
4554))
else
(if i.val < 2326 then
(if i.val < 2325 then
4555
else
3267)
else
(if i.val < 2327 then
4556
else
4557)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
4558
else
4559)
else
(if i.val < 2331 then
2570
else
1393))
else
(if i.val < 2334 then
(if i.val < 2333 then
4560
else
4561)
else
(if i.val < 2335 then
4562
else
4563)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
4448
else
4323)
else
(if i.val < 2339 then
4564
else
4449))
else
(if i.val < 2342 then
(if i.val < 2341 then
4450
else
4451)
else
(if i.val < 2343 then
4565
else
4566)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
3122
else
2648)
else
(if i.val < 2347 then
4567
else
4568))
else
(if i.val < 2350 then
(if i.val < 2349 then
4569
else
4570)
else
(if i.val < 2351 then
2321
else
4571))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
4572
else
4573)
else
(if i.val < 2355 then
4574
else
4575))
else
(if i.val < 2358 then
(if i.val < 2357 then
4227
else
418)
else
(if i.val < 2359 then
419
else
420)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
422
else
426)
else
(if i.val < 2363 then
427
else
428))
else
(if i.val < 2366 then
(if i.val < 2365 then
437
else
438)
else
(if i.val < 2367 then
439
else
441))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
442
else
464)
else
(if i.val < 2371 then
465
else
467))
else
(if i.val < 2374 then
(if i.val < 2373 then
468
else
469)
else
(if i.val < 2375 then
470
else
471)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
472
else
473)
else
(if i.val < 2379 then
474
else
475))
else
(if i.val < 2382 then
(if i.val < 2381 then
476
else
477)
else
(if i.val < 2383 then
478
else
4576))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
2443
else
4577)
else
(if i.val < 2387 then
4578
else
1207))
else
(if i.val < 2390 then
(if i.val < 2389 then
4579
else
4580)
else
(if i.val < 2391 then
4581
else
2432)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
4582
else
3721)
else
(if i.val < 2395 then
3330
else
4583))
else
(if i.val < 2398 then
(if i.val < 2397 then
1093
else
3627)
else
(if i.val < 2399 then
4584
else
4585)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
4586
else
4587)
else
(if i.val < 2403 then
4588
else
4336))
else
(if i.val < 2406 then
(if i.val < 2405 then
4589
else
4590)
else
(if i.val < 2407 then
4591
else
4592)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
4593
else
4594)
else
(if i.val < 2411 then
4595
else
2153))
else
(if i.val < 2414 then
(if i.val < 2413 then
669
else
4596)
else
(if i.val < 2415 then
4597
else
2445))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
2472
else
4598)
else
(if i.val < 2419 then
630
else
4599))
else
(if i.val < 2422 then
(if i.val < 2421 then
2518
else
4201)
else
(if i.val < 2423 then
2181
else
4600)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
2486
else
4601)
else
(if i.val < 2427 then
4602
else
4603))
else
(if i.val < 2430 then
(if i.val < 2429 then
4604
else
4605)
else
(if i.val < 2431 then
4606
else
4607)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
1103
else
4166)
else
(if i.val < 2435 then
3334
else
3687))
else
(if i.val < 2438 then
(if i.val < 2437 then
2612
else
2577)
else
(if i.val < 2439 then
4608
else
4609)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
4610
else
1577)
else
(if i.val < 2443 then
1661
else
1095))
else
(if i.val < 2446 then
(if i.val < 2445 then
1832
else
3154)
else
(if i.val < 2447 then
4611
else
1024))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
4612
else
4613)
else
(if i.val < 2451 then
4614
else
4615))
else
(if i.val < 2454 then
(if i.val < 2453 then
4616
else
4617)
else
(if i.val < 2455 then
4618
else
1398)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
4191
else
3263)
else
(if i.val < 2459 then
4619
else
3200))
else
(if i.val < 2462 then
(if i.val < 2461 then
4620
else
4621)
else
(if i.val < 2463 then
4622
else
4623)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
4624
else
4625)
else
(if i.val < 2467 then
4626
else
4627))
else
(if i.val < 2470 then
(if i.val < 2469 then
4628
else
4208)
else
(if i.val < 2471 then
4629
else
4630)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
2307
else
2205)
else
(if i.val < 2475 then
4631
else
2575))
else
(if i.val < 2478 then
(if i.val < 2477 then
4772
else
4922)
else
(if i.val < 2479 then
5019
else
5189))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
5190
else
5191)
else
(if i.val < 2483 then
5122
else
5192))
else
(if i.val < 2486 then
(if i.val < 2485 then
5193
else
1264)
else
(if i.val < 2487 then
5194
else
1092)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
4773
else
2526)
else
(if i.val < 2491 then
4736
else
4737))
else
(if i.val < 2494 then
(if i.val < 2493 then
490
else
2523)
else
(if i.val < 2495 then
1657
else
4128))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
921
else
931)
else
(if i.val < 2499 then
2598
else
1252))
else
(if i.val < 2502 then
(if i.val < 2501 then
1145
else
5020)
else
(if i.val < 2503 then
3716
else
3673)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
2055
else
4760)
else
(if i.val < 2507 then
936
else
951))
else
(if i.val < 2510 then
(if i.val < 2509 then
5195
else
4766)
else
(if i.val < 2511 then
5196
else
5197))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
487
else
4486)
else
(if i.val < 2515 then
3647
else
2500))
else
(if i.val < 2518 then
(if i.val < 2517 then
4712
else
1260)
else
(if i.val < 2519 then
4713
else
4733)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
4734
else
4735)
else
(if i.val < 2523 then
4774
else
4775))
else
(if i.val < 2526 then
(if i.val < 2525 then
3742
else
4776)
else
(if i.val < 2527 then
1128
else
4777)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
500
else
4127)
else
(if i.val < 2531 then
4868
else
965))
else
(if i.val < 2534 then
(if i.val < 2533 then
4881
else
4882)
else
(if i.val < 2535 then
4883
else
4923)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
4924
else
4925)
else
(if i.val < 2539 then
1752
else
1524))
else
(if i.val < 2542 then
(if i.val < 2541 then
1176
else
4926)
else
(if i.val < 2543 then
2778
else
1129))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
2522
else
623)
else
(if i.val < 2547 then
3753
else
5021))
else
(if i.val < 2550 then
(if i.val < 2549 then
5022
else
5023)
else
(if i.val < 2551 then
5024
else
5025)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
4954
else
5026)
else
(if i.val < 2555 then
3204
else
5198))
else
(if i.val < 2558 then
(if i.val < 2557 then
5199
else
5200)
else
(if i.val < 2559 then
5201
else
4203)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0005 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
5202
else
1250)
else
(if i.val < 2563 then
1681
else
5203))
else
(if i.val < 2566 then
(if i.val < 2565 then
5204
else
5205)
else
(if i.val < 2567 then
5206
else
5207)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
1838
else
5208)
else
(if i.val < 2571 then
981
else
5209))
else
(if i.val < 2574 then
(if i.val < 2573 then
4409
else
5210)
else
(if i.val < 2575 then
5211
else
5212))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
4478
else
5213)
else
(if i.val < 2579 then
5214
else
5215))
else
(if i.val < 2582 then
(if i.val < 2581 then
1453
else
5216)
else
(if i.val < 2583 then
2638
else
4941)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
5217
else
5218)
else
(if i.val < 2587 then
4927
else
5219))
else
(if i.val < 2590 then
(if i.val < 2589 then
5220
else
5221)
else
(if i.val < 2591 then
5222
else
4888)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
4872
else
4125)
else
(if i.val < 2595 then
4942
else
4943))
else
(if i.val < 2598 then
(if i.val < 2597 then
4944
else
5223)
else
(if i.val < 2599 then
5224
else
5225)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
5226
else
2297)
else
(if i.val < 2603 then
5227
else
5228))
else
(if i.val < 2606 then
(if i.val < 2605 then
4975
else
5229)
else
(if i.val < 2607 then
5230
else
5231))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
5232
else
5233)
else
(if i.val < 2611 then
4915
else
5234))
else
(if i.val < 2614 then
(if i.val < 2613 then
5072
else
4473)
else
(if i.val < 2615 then
4813
else
5027)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
5028
else
5029)
else
(if i.val < 2619 then
3056
else
3055))
else
(if i.val < 2622 then
(if i.val < 2621 then
3059
else
4930)
else
(if i.val < 2623 then
4931
else
5032))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
5033
else
1656)
else
(if i.val < 2627 then
1598
else
5034))
else
(if i.val < 2630 then
(if i.val < 2629 then
4945
else
4116)
else
(if i.val < 2631 then
501
else
4946)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
4947
else
4948)
else
(if i.val < 2635 then
4949
else
4244))
else
(if i.val < 2638 then
(if i.val < 2637 then
4950
else
4656)
else
(if i.val < 2639 then
3070
else
4951))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
4090
else
5235)
else
(if i.val < 2643 then
5236
else
5237))
else
(if i.val < 2646 then
(if i.val < 2645 then
2988
else
5238)
else
(if i.val < 2647 then
5239
else
1647)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
1015
else
5240)
else
(if i.val < 2651 then
5241
else
5242))
else
(if i.val < 2654 then
(if i.val < 2653 then
2296
else
4512)
else
(if i.val < 2655 then
5086
else
5243)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
2427
else
5244)
else
(if i.val < 2659 then
5245
else
5246))
else
(if i.val < 2662 then
(if i.val < 2661 then
5247
else
1289)
else
(if i.val < 2663 then
5121
else
5248)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
5249
else
1285)
else
(if i.val < 2667 then
4803
else
5250))
else
(if i.val < 2670 then
(if i.val < 2669 then
5251
else
5252)
else
(if i.val < 2671 then
5253
else
728))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
5254
else
3277)
else
(if i.val < 2675 then
2748
else
3521))
else
(if i.val < 2678 then
(if i.val < 2677 then
1216
else
2744)
else
(if i.val < 2679 then
4778
else
2543)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
4633
else
1133)
else
(if i.val < 2683 then
5030
else
4640))
else
(if i.val < 2686 then
(if i.val < 2685 then
5031
else
482)
else
(if i.val < 2687 then
488
else
489)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
491
else
492)
else
(if i.val < 2691 then
528
else
529))
else
(if i.val < 2694 then
(if i.val < 2693 then
530
else
531)
else
(if i.val < 2695 then
532
else
533)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
534
else
535)
else
(if i.val < 2699 then
537
else
2499))
else
(if i.val < 2702 then
(if i.val < 2701 then
5035
else
5036)
else
(if i.val < 2703 then
5037
else
5038))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
5039
else
5040)
else
(if i.val < 2707 then
5041
else
2517))
else
(if i.val < 2710 then
(if i.val < 2709 then
4635
else
3311)
else
(if i.val < 2711 then
2485
else
2641)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
4870
else
4928)
else
(if i.val < 2715 then
4929
else
499))
else
(if i.val < 2718 then
(if i.val < 2717 then
502
else
509)
else
(if i.val < 2719 then
510
else
511)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
4932
else
4933)
else
(if i.val < 2723 then
1454
else
4934))
else
(if i.val < 2726 then
(if i.val < 2725 then
1172
else
4935)
else
(if i.val < 2727 then
4936
else
1174)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
923
else
1112)
else
(if i.val < 2731 then
1431
else
4937))
else
(if i.val < 2734 then
(if i.val < 2733 then
4938
else
4939)
else
(if i.val < 2735 then
2767
else
1751))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
4940
else
5042)
else
(if i.val < 2739 then
5043
else
4238))
else
(if i.val < 2742 then
(if i.val < 2741 then
4990
else
5044)
else
(if i.val < 2743 then
5045
else
5046)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
5047
else
4802)
else
(if i.val < 2747 then
5048
else
4741))
else
(if i.val < 2750 then
(if i.val < 2749 then
5049
else
5050)
else
(if i.val < 2751 then
1210
else
5051))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
5052
else
5053)
else
(if i.val < 2755 then
3044
else
5054))
else
(if i.val < 2758 then
(if i.val < 2757 then
5055
else
5056)
else
(if i.val < 2759 then
2997
else
5057)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
5058
else
5129)
else
(if i.val < 2763 then
4648
else
5255))
else
(if i.val < 2766 then
(if i.val < 2765 then
3696
else
4345)
else
(if i.val < 2767 then
1473
else
3692))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
4294
else
2590)
else
(if i.val < 2771 then
3682
else
5256))
else
(if i.val < 2774 then
(if i.val < 2773 then
650
else
4837)
else
(if i.val < 2775 then
3139
else
5257)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
5258
else
1669)
else
(if i.val < 2779 then
5259
else
5260))
else
(if i.val < 2782 then
(if i.val < 2781 then
5261
else
5262)
else
(if i.val < 2783 then
651
else
1413)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
2132
else
5016)
else
(if i.val < 2787 then
1267
else
1280))
else
(if i.val < 2790 then
(if i.val < 2789 then
1814
else
4501)
else
(if i.val < 2791 then
1509
else
2168)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
5263
else
5264)
else
(if i.val < 2795 then
5265
else
5266))
else
(if i.val < 2798 then
(if i.val < 2797 then
2788
else
3737)
else
(if i.val < 2799 then
5008
else
5267))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
5268
else
5269)
else
(if i.val < 2803 then
5270
else
5271))
else
(if i.val < 2806 then
(if i.val < 2805 then
5272
else
4997)
else
(if i.val < 2807 then
5273
else
5274)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
5275
else
5276)
else
(if i.val < 2811 then
5277
else
2494))
else
(if i.val < 2814 then
(if i.val < 2813 then
5278
else
916)
else
(if i.val < 2815 then
5279
else
5280))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
4157
else
5281)
else
(if i.val < 2819 then
5282
else
5283))
else
(if i.val < 2822 then
(if i.val < 2821 then
910
else
5284)
else
(if i.val < 2823 then
5285
else
5286)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
4086
else
3773)
else
(if i.val < 2827 then
5287
else
4681))
else
(if i.val < 2830 then
(if i.val < 2829 then
4903
else
2724)
else
(if i.val < 2831 then
2727
else
2540))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
4792
else
4745)
else
(if i.val < 2835 then
5065
else
5066))
else
(if i.val < 2838 then
(if i.val < 2837 then
5288
else
5289)
else
(if i.val < 2839 then
3386
else
5290)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
5067
else
5068)
else
(if i.val < 2843 then
3468
else
5069))
else
(if i.val < 2846 then
(if i.val < 2845 then
1130
else
3075)
else
(if i.val < 2847 then
4901
else
5291)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
2750
else
5292)
else
(if i.val < 2851 then
5293
else
5294))
else
(if i.val < 2854 then
(if i.val < 2853 then
2987
else
5295)
else
(if i.val < 2855 then
2676
else
3462)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
3196
else
4976)
else
(if i.val < 2859 then
2786
else
5296))
else
(if i.val < 2862 then
(if i.val < 2861 then
5297
else
3128)
else
(if i.val < 2863 then
5298
else
3279))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
5299
else
5300)
else
(if i.val < 2867 then
4115
else
2787))
else
(if i.val < 2870 then
(if i.val < 2869 then
761
else
3165)
else
(if i.val < 2871 then
5301
else
4808)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
2665
else
5302)
else
(if i.val < 2875 then
5303
else
5304))
else
(if i.val < 2878 then
(if i.val < 2877 then
2661
else
480)
else
(if i.val < 2879 then
493
else
494))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
495
else
496)
else
(if i.val < 2883 then
497
else
498))
else
(if i.val < 2886 then
(if i.val < 2885 then
503
else
512)
else
(if i.val < 2887 then
513
else
514)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
515
else
538)
else
(if i.val < 2891 then
539
else
540))
else
(if i.val < 2894 then
(if i.val < 2893 then
541
else
543)
else
(if i.val < 2895 then
544
else
545))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
546
else
547)
else
(if i.val < 2899 then
548
else
549))
else
(if i.val < 2902 then
(if i.val < 2901 then
550
else
551)
else
(if i.val < 2903 then
600
else
602)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
603
else
604)
else
(if i.val < 2907 then
606
else
607))
else
(if i.val < 2910 then
(if i.val < 2909 then
608
else
610)
else
(if i.val < 2911 then
611
else
612)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
613
else
614)
else
(if i.val < 2915 then
616
else
617))
else
(if i.val < 2918 then
(if i.val < 2917 then
619
else
620)
else
(if i.val < 2919 then
621
else
622)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
624
else
625)
else
(if i.val < 2923 then
626
else
627))
else
(if i.val < 2926 then
(if i.val < 2925 then
628
else
5305)
else
(if i.val < 2927 then
3202
else
5306))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
5307
else
5308)
else
(if i.val < 2931 then
5309
else
1026))
else
(if i.val < 2934 then
(if i.val < 2933 then
2144
else
2455)
else
(if i.val < 2935 then
3303
else
5310)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
3609
else
1159)
else
(if i.val < 2939 then
1660
else
5311))
else
(if i.val < 2942 then
(if i.val < 2941 then
5312
else
4304)
else
(if i.val < 2943 then
2989
else
5313)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
5314
else
4310)
else
(if i.val < 2947 then
2783
else
3029))
else
(if i.val < 2950 then
(if i.val < 2949 then
5315
else
5316)
else
(if i.val < 2951 then
5317
else
5318)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
5319
else
3084)
else
(if i.val < 2955 then
1389
else
3031))
else
(if i.val < 2958 then
(if i.val < 2957 then
4311
else
2154)
else
(if i.val < 2959 then
5320
else
5321))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
2730
else
5322)
else
(if i.val < 2963 then
5114
else
5323))
else
(if i.val < 2966 then
(if i.val < 2965 then
5324
else
3066)
else
(if i.val < 2967 then
5325
else
3060)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
3698
else
5326)
else
(if i.val < 2971 then
5327
else
5328))
else
(if i.val < 2974 then
(if i.val < 2973 then
5329
else
3039)
else
(if i.val < 2975 then
5103
else
5330)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
5331
else
5332)
else
(if i.val < 2979 then
5333
else
2722))
else
(if i.val < 2982 then
(if i.val < 2981 then
2038
else
3389)
else
(if i.val < 2983 then
5334
else
659)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
5335
else
4729)
else
(if i.val < 2987 then
774
else
1214))
else
(if i.val < 2990 then
(if i.val < 2989 then
5336
else
1408)
else
(if i.val < 2991 then
3034
else
5337))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
5338
else
4346)
else
(if i.val < 2995 then
2195
else
663))
else
(if i.val < 2998 then
(if i.val < 2997 then
3315
else
3100)
else
(if i.val < 2999 then
5339
else
4989)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
2604
else
5340)
else
(if i.val < 3003 then
5341
else
5342))
else
(if i.val < 3006 then
(if i.val < 3005 then
5343
else
5344)
else
(if i.val < 3007 then
5345
else
1008))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
4417
else
5346)
else
(if i.val < 3011 then
5347
else
5348))
else
(if i.val < 3014 then
(if i.val < 3013 then
4173
else
5349)
else
(if i.val < 3015 then
5350
else
5351)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
5352
else
5353)
else
(if i.val < 3019 then
3130
else
5354))
else
(if i.val < 3022 then
(if i.val < 3021 then
1675
else
5355)
else
(if i.val < 3023 then
5356
else
5357))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
2567
else
5358)
else
(if i.val < 3027 then
5359
else
5360))
else
(if i.val < 3030 then
(if i.val < 3029 then
5361
else
1414)
else
(if i.val < 3031 then
5362
else
1425)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
2097
else
5363)
else
(if i.val < 3035 then
5364
else
5365))
else
(if i.val < 3038 then
(if i.val < 3037 then
5366
else
5367)
else
(if i.val < 3039 then
5368
else
1446)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
3313
else
5369)
else
(if i.val < 3043 then
4961
else
5370))
else
(if i.val < 3046 then
(if i.val < 3045 then
1611
else
5371)
else
(if i.val < 3047 then
2991
else
5372)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
5373
else
5374)
else
(if i.val < 3051 then
3058
else
4720))
else
(if i.val < 3054 then
(if i.val < 3053 then
5375
else
5376)
else
(if i.val < 3055 then
2411
else
1236))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
1151
else
5377)
else
(if i.val < 3059 then
5378
else
1240))
else
(if i.val < 3062 then
(if i.val < 3061 then
1439
else
5379)
else
(if i.val < 3063 then
1797
else
677)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
5380
else
5381)
else
(if i.val < 3067 then
1437
else
4728))
else
(if i.val < 3070 then
(if i.val < 3069 then
5382
else
5383)
else
(if i.val < 3071 then
2582
else
5384)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0006 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
3098
else
3314)
else
(if i.val < 3075 then
5385
else
1206))
else
(if i.val < 3078 then
(if i.val < 3077 then
5386
else
3104)
else
(if i.val < 3079 then
5387
else
5388)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
2449
else
3219)
else
(if i.val < 3083 then
5389
else
5390))
else
(if i.val < 3086 then
(if i.val < 3085 then
1423
else
5119)
else
(if i.val < 3087 then
5391
else
5392))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
5393
else
2549)
else
(if i.val < 3091 then
3613
else
5394))
else
(if i.val < 3094 then
(if i.val < 3093 then
5395
else
3395)
else
(if i.val < 3095 then
3317
else
5396)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
5397
else
5398)
else
(if i.val < 3099 then
5399
else
3011))
else
(if i.val < 3102 then
(if i.val < 3101 then
2758
else
2756)
else
(if i.val < 3103 then
5400
else
5401)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
5402
else
4112)
else
(if i.val < 3107 then
1395
else
5865))
else
(if i.val < 3110 then
(if i.val < 3109 then
5603
else
5438)
else
(if i.val < 3111 then
6066
else
6016)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
5140
else
6321)
else
(if i.val < 3115 then
4205
else
6322))
else
(if i.val < 3118 then
(if i.val < 3117 then
6323
else
6324)
else
(if i.val < 3119 then
6325
else
6326))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
6209
else
5150)
else
(if i.val < 3123 then
1014
else
5105))
else
(if i.val < 3126 then
(if i.val < 3125 then
3021
else
3720)
else
(if i.val < 3127 then
3769
else
6327)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
1271
else
6328)
else
(if i.val < 3131 then
6329
else
6330))
else
(if i.val < 3134 then
(if i.val < 3133 then
638
else
5675)
else
(if i.val < 3135 then
3140
else
5602))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
3155
else
3503)
else
(if i.val < 3139 then
5604
else
1269))
else
(if i.val < 3142 then
(if i.val < 3141 then
1506
else
6067)
else
(if i.val < 3143 then
3641
else
1541)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
5866
else
4168)
else
(if i.val < 3147 then
688
else
5951))
else
(if i.val < 3150 then
(if i.val < 3149 then
3351
else
1645)
else
(if i.val < 3151 then
1587
else
2441))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
2745
else
4698)
else
(if i.val < 3155 then
2415
else
1471))
else
(if i.val < 3158 then
(if i.val < 3157 then
1537
else
6068)
else
(if i.val < 3159 then
5860
else
5857)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
4662
else
4677)
else
(if i.val < 3163 then
6069
else
5501))
else
(if i.val < 3166 then
(if i.val < 3165 then
5862
else
1282)
else
(if i.val < 3167 then
6070
else
2446)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
4863
else
6331)
else
(if i.val < 3171 then
5653
else
5649))
else
(if i.val < 3174 then
(if i.val < 3173 then
6332
else
5652)
else
(if i.val < 3175 then
641
else
5648)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
4700
else
1575)
else
(if i.val < 3179 then
4676
else
2574))
else
(if i.val < 3182 then
(if i.val < 3181 then
4898
else
5665)
else
(if i.val < 3183 then
5666
else
4261))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
5667
else
6333)
else
(if i.val < 3187 then
5671
else
4254))
else
(if i.val < 3190 then
(if i.val < 3189 then
648
else
649)
else
(if i.val < 3191 then
1529
else
1474)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
2790
else
5143)
else
(if i.val < 3195 then
5177
else
629))
else
(if i.val < 3198 then
(if i.val < 3197 then
1265
else
5566)
else
(if i.val < 3199 then
5598
else
5567)))))))
else
(if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
5568
else
5569)
else
(if i.val < 3203 then
1384
else
5599))
else
(if i.val < 3206 then
(if i.val < 3205 then
5600
else
5601)
else
(if i.val < 3207 then
3448
else
2180)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
5676
else
5677)
else
(if i.val < 3211 then
5678
else
5679))
else
(if i.val < 3214 then
(if i.val < 3213 then
5680
else
685)
else
(if i.val < 3215 then
4835
else
4843))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
3329
else
1653)
else
(if i.val < 3219 then
5837
else
5838))
else
(if i.val < 3222 then
(if i.val < 3221 then
5867
else
5868)
else
(if i.val < 3223 then
2183
else
5869)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
5870
else
1570)
else
(if i.val < 3227 then
5871
else
3491))
else
(if i.val < 3230 then
(if i.val < 3229 then
1571
else
3350)
else
(if i.val < 3231 then
800
else
5952)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
5953
else
4508)
else
(if i.val < 3235 then
2088
else
5954))
else
(if i.val < 3238 then
(if i.val < 3237 then
5729
else
5955)
else
(if i.val < 3239 then
5956
else
5957)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
3713
else
6071)
else
(if i.val < 3243 then
6072
else
1643))
else
(if i.val < 3246 then
(if i.val < 3245 then
6073
else
4637)
else
(if i.val < 3247 then
6074
else
6075))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
6076
else
4479)
else
(if i.val < 3251 then
5608
else
6077))
else
(if i.val < 3254 then
(if i.val < 3253 then
5624
else
4339)
else
(if i.val < 3255 then
5431
else
6078)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
6079
else
4827)
else
(if i.val < 3259 then
6080
else
6081))
else
(if i.val < 3262 then
(if i.val < 3261 then
6334
else
6335)
else
(if i.val < 3263 then
3355
else
6336))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
6337
else
5477)
else
(if i.val < 3267 then
6033
else
6338))
else
(if i.val < 3270 then
(if i.val < 3269 then
6339
else
4717)
else
(if i.val < 3271 then
4148
else
6340)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
3666
else
6341)
else
(if i.val < 3275 then
6342
else
5789))
else
(if i.val < 3278 then
(if i.val < 3277 then
3062
else
1160)
else
(if i.val < 3279 then
6343
else
1273))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
1755
else
6228)
else
(if i.val < 3283 then
6344
else
6345))
else
(if i.val < 3286 then
(if i.val < 3285 then
6346
else
2440)
else
(if i.val < 3287 then
2085
else
1664)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
6347
else
6348)
else
(if i.val < 3291 then
6349
else
6350))
else
(if i.val < 3294 then
(if i.val < 3293 then
6351
else
990)
else
(if i.val < 3295 then
6034
else
5502)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
6352
else
3610)
else
(if i.val < 3299 then
1803
else
6353))
else
(if i.val < 3302 then
(if i.val < 3301 then
5902
else
6354)
else
(if i.val < 3303 then
6355
else
1399)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
6356
else
6357)
else
(if i.val < 3307 then
6358
else
6359))
else
(if i.val < 3310 then
(if i.val < 3309 then
6360
else
6361)
else
(if i.val < 3311 then
6362
else
1263))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
6363
else
6364)
else
(if i.val < 3315 then
6160
else
5083))
else
(if i.val < 3318 then
(if i.val < 3317 then
3107
else
5836)
else
(if i.val < 3319 then
6365
else
3734)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
6366
else
6367)
else
(if i.val < 3323 then
5959
else
6368))
else
(if i.val < 3326 then
(if i.val < 3325 then
3363
else
5976)
else
(if i.val < 3327 then
4650
else
3360))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
3776
else
6281)
else
(if i.val < 3331 then
1107
else
642))
else
(if i.val < 3334 then
(if i.val < 3333 then
2723
else
6369)
else
(if i.val < 3335 then
1490
else
6370)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
5634
else
6371)
else
(if i.val < 3339 then
4857
else
2655))
else
(if i.val < 3342 then
(if i.val < 3341 then
6372
else
6373)
else
(if i.val < 3343 then
5958
else
6084))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
6085
else
4199)
else
(if i.val < 3347 then
5081
else
6012))
else
(if i.val < 3350 then
(if i.val < 3349 then
2161
else
3507)
else
(if i.val < 3351 then
6374
else
6375)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
793
else
686)
else
(if i.val < 3355 then
5886
else
5842))
else
(if i.val < 3358 then
(if i.val < 3357 then
3036
else
5887)
else
(if i.val < 3359 then
5888
else
4182)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
5977
else
5978)
else
(if i.val < 3363 then
3705
else
1589))
else
(if i.val < 3366 then
(if i.val < 3365 then
5979
else
6376)
else
(if i.val < 3367 then
6377
else
6378)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
6379
else
2731)
else
(if i.val < 3371 then
6236
else
6266))
else
(if i.val < 3374 then
(if i.val < 3373 then
6380
else
718)
else
(if i.val < 3375 then
3490
else
678))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
6381
else
5923)
else
(if i.val < 3379 then
6382
else
4295))
else
(if i.val < 3382 then
(if i.val < 3381 then
6383
else
6384)
else
(if i.val < 3383 then
6385
else
6386)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
6387
else
6388)
else
(if i.val < 3387 then
1185
else
6389))
else
(if i.val < 3390 then
(if i.val < 3389 then
6390
else
6391)
else
(if i.val < 3391 then
1583
else
5941))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
4378
else
6392)
else
(if i.val < 3395 then
6393
else
6394))
else
(if i.val < 3398 then
(if i.val < 3397 then
6395
else
4977)
else
(if i.val < 3399 then
3095
else
5681)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
6082
else
6086)
else
(if i.val < 3403 then
6087
else
6088))
else
(if i.val < 3406 then
(if i.val < 3405 then
6089
else
2539)
else
(if i.val < 3407 then
4130
else
653))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
749
else
5960)
else
(if i.val < 3411 then
3735
else
753))
else
(if i.val < 3414 then
(if i.val < 3413 then
754
else
4206)
else
(if i.val < 3415 then
5964
else
5965)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
5454
else
5702)
else
(if i.val < 3419 then
6093
else
6094))
else
(if i.val < 3422 then
(if i.val < 3421 then
6095
else
6096)
else
(if i.val < 3423 then
998
else
6097)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
6098
else
2735)
else
(if i.val < 3427 then
2538
else
3441))
else
(if i.val < 3430 then
(if i.val < 3429 then
5844
else
5980)
else
(if i.val < 3431 then
5981
else
680)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
687
else
707)
else
(if i.val < 3435 then
708
else
709))
else
(if i.val < 3438 then
(if i.val < 3437 then
5982
else
5983)
else
(if i.val < 3439 then
5984
else
3749))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
5985
else
1573)
else
(if i.val < 3443 then
4651
else
5986))
else
(if i.val < 3446 then
(if i.val < 3445 then
4661
else
3752)
else
(if i.val < 3447 then
5987
else
2110)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
4218
else
4220)
else
(if i.val < 3451 then
5988
else
5989))
else
(if i.val < 3454 then
(if i.val < 3453 then
1815
else
3522)
else
(if i.val < 3455 then
6396
else
5998)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
6216
else
4308)
else
(if i.val < 3459 then
6397
else
1780))
else
(if i.val < 3462 then
(if i.val < 3461 then
5463
else
5709)
else
(if i.val < 3463 then
1217
else
3770)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
5462
else
1777)
else
(if i.val < 3467 then
6398
else
3514))
else
(if i.val < 3470 then
(if i.val < 3469 then
1202
else
2061)
else
(if i.val < 3471 then
779
else
4181))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
2295
else
6217)
else
(if i.val < 3475 then
6399
else
2592))
else
(if i.val < 3478 then
(if i.val < 3477 then
1843
else
4222)
else
(if i.val < 3479 then
5148
else
5723)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
4718
else
3023)
else
(if i.val < 3483 then
6400
else
6401))
else
(if i.val < 3486 then
(if i.val < 3485 then
3483
else
6402)
else
(if i.val < 3487 then
6403
else
6099)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
5736
else
1553)
else
(if i.val < 3491 then
5803
else
6404))
else
(if i.val < 3494 then
(if i.val < 3493 then
6405
else
5818)
else
(if i.val < 3495 then
1829
else
6207)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
1837
else
6406)
else
(if i.val < 3499 then
6015
else
6265))
else
(if i.val < 3502 then
(if i.val < 3501 then
6407
else
4307)
else
(if i.val < 3503 then
6408
else
6409))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
6410
else
6411)
else
(if i.val < 3507 then
6412
else
5623))
else
(if i.val < 3510 then
(if i.val < 3509 then
6413
else
6414)
else
(if i.val < 3511 then
6415
else
1097)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
2602
else
6416)
else
(if i.val < 3515 then
6009
else
3643))
else
(if i.val < 3518 then
(if i.val < 3517 then
6417
else
6418)
else
(if i.val < 3519 then
6060
else
6419))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
1677
else
1683)
else
(if i.val < 3523 then
2266
else
789))
else
(if i.val < 3526 then
(if i.val < 3525 then
6420
else
6421)
else
(if i.val < 3527 then
3629
else
5682)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
2766
else
5848)
else
(if i.val < 3531 then
6083
else
4999))
else
(if i.val < 3534 then
(if i.val < 3533 then
6090
else
5423)
else
(if i.val < 3535 then
6091
else
6092))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
2165
else
5424)
else
(if i.val < 3539 then
3156
else
4174))
else
(if i.val < 3542 then
(if i.val < 3541 then
5532
else
637)
else
(if i.val < 3543 then
639
else
655)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
656
else
657)
else
(if i.val < 3547 then
661
else
662))
else
(if i.val < 3550 then
(if i.val < 3549 then
665
else
755)
else
(if i.val < 3551 then
756
else
757)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
758
else
759)
else
(if i.val < 3555 then
760
else
765))
else
(if i.val < 3558 then
(if i.val < 3557 then
766
else
767)
else
(if i.val < 3559 then
768
else
769)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
770
else
771)
else
(if i.val < 3563 then
772
else
776))
else
(if i.val < 3566 then
(if i.val < 3565 then
4866
else
4158)
else
(if i.val < 3567 then
3280
else
4889))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
6100
else
6101)
else
(if i.val < 3571 then
6102
else
6103))
else
(if i.val < 3574 then
(if i.val < 3573 then
1684
else
6104)
else
(if i.val < 3575 then
4423
else
1680)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
5893
else
6105)
else
(if i.val < 3579 then
6106
else
6107))
else
(if i.val < 3582 then
(if i.val < 3581 then
5415
else
2179)
else
(if i.val < 3583 then
3465
else
2147)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0007 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
3459
else
4204)
else
(if i.val < 3587 then
3366
else
2414))
else
(if i.val < 3590 then
(if i.val < 3589 then
5772
else
1576)
else
(if i.val < 3591 then
5961
else
5962)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
5963
else
689)
else
(if i.val < 3595 then
690
else
710))
else
(if i.val < 3598 then
(if i.val < 3597 then
711
else
712)
else
(if i.val < 3599 then
713
else
3382))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
3328
else
1415)
else
(if i.val < 3603 then
2182
else
2173))
else
(if i.val < 3606 then
(if i.val < 3605 then
5966
else
5967)
else
(if i.val < 3607 then
3346
else
5775)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
1841
else
1402)
else
(if i.val < 3611 then
5968
else
5969))
else
(if i.val < 3614 then
(if i.val < 3613 then
5970
else
5971)
else
(if i.val < 3615 then
2131
else
2130)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
2057
else
5972)
else
(if i.val < 3619 then
3727
else
5973))
else
(if i.val < 3622 then
(if i.val < 3621 then
5974
else
3690)
else
(if i.val < 3623 then
1750
else
5137)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
5975
else
6019)
else
(if i.val < 3627 then
5784
else
1110))
else
(if i.val < 3630 then
(if i.val < 3629 then
6108
else
5530)
else
(if i.val < 3631 then
5792
else
6109))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
6110
else
6111)
else
(if i.val < 3635 then
4715
else
5928))
else
(if i.val < 3638 then
(if i.val < 3637 then
6030
else
6112)
else
(if i.val < 3639 then
6113
else
6114)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
6115
else
6116)
else
(if i.val < 3643 then
6117
else
4716))
else
(if i.val < 3646 then
(if i.val < 3645 then
6062
else
6118)
else
(if i.val < 3647 then
972
else
1144))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
1659
else
1674)
else
(if i.val < 3651 then
6049
else
4855))
else
(if i.val < 3654 then
(if i.val < 3653 then
6119
else
6120)
else
(if i.val < 3655 then
3092
else
6121)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
6122
else
5613)
else
(if i.val < 3659 then
1673
else
6123))
else
(if i.val < 3662 then
(if i.val < 3661 then
1676
else
3501)
else
(if i.val < 3663 then
6124
else
957))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
6125
else
4101)
else
(if i.val < 3667 then
5570
else
6126))
else
(if i.val < 3670 then
(if i.val < 3669 then
6127
else
6128)
else
(if i.val < 3671 then
939
else
6129)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
6130
else
4099)
else
(if i.val < 3675 then
4211
else
4209))
else
(if i.val < 3678 then
(if i.val < 3677 then
6131
else
6214)
else
(if i.val < 3679 then
6218
else
6219)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
6422
else
6423)
else
(if i.val < 3683 then
6424
else
4104))
else
(if i.val < 3686 then
(if i.val < 3685 then
4972
else
6425)
else
(if i.val < 3687 then
1651
else
1743)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
6426
else
4840)
else
(if i.val < 3691 then
2311
else
5997))
else
(if i.val < 3694 then
(if i.val < 3693 then
2734
else
6427)
else
(if i.val < 3695 then
6428
else
6429))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
6430
else
2305)
else
(if i.val < 3699 then
1440
else
4320))
else
(if i.val < 3702 then
(if i.val < 3701 then
3755
else
4365)
else
(if i.val < 3703 then
5790
else
6251)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
783
else
4321)
else
(if i.val < 3707 then
1543
else
6431))
else
(if i.val < 3710 then
(if i.val < 3709 then
5819
else
6432)
else
(if i.val < 3711 then
6259
else
6433)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
6434
else
6435)
else
(if i.val < 3715 then
6436
else
5732))
else
(if i.val < 3718 then
(if i.val < 3717 then
6437
else
6438)
else
(if i.val < 3719 then
2209
else
2082)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
6439
else
1105)
else
(if i.val < 3723 then
4862
else
5440))
else
(if i.val < 3726 then
(if i.val < 3725 then
1821
else
6287)
else
(if i.val < 3727 then
726
else
5085))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
6440
else
6441)
else
(if i.val < 3731 then
6028
else
6442))
else
(if i.val < 3734 then
(if i.val < 3733 then
5430
else
6443)
else
(if i.val < 3735 then
1515
else
1725)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
3238
else
6235)
else
(if i.val < 3739 then
6227
else
4820))
else
(if i.val < 3742 then
(if i.val < 3741 then
3725
else
1825)
else
(if i.val < 3743 then
4498
else
1822)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
5783
else
6444)
else
(if i.val < 3747 then
5437
else
6445))
else
(if i.val < 3750 then
(if i.val < 3749 then
6446
else
1642)
else
(if i.val < 3751 then
6447
else
4846)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
6448
else
6449)
else
(if i.val < 3755 then
3513
else
6450))
else
(if i.val < 3758 then
(if i.val < 3757 then
2042
else
6451)
else
(if i.val < 3759 then
6452
else
3688))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
6453
else
6454)
else
(if i.val < 3763 then
6455
else
4322))
else
(if i.val < 3766 then
(if i.val < 3765 then
6039
else
6456)
else
(if i.val < 3767 then
6457
else
6063)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
6458
else
2134)
else
(if i.val < 3771 then
6459
else
3451))
else
(if i.val < 3774 then
(if i.val < 3773 then
5004
else
1167)
else
(if i.val < 3775 then
5589
else
6022))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
3600
else
4102)
else
(if i.val < 3779 then
4906
else
4242))
else
(if i.val < 3782 then
(if i.val < 3781 then
6460
else
6461)
else
(if i.val < 3783 then
1401
else
4965)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
6462
else
6463)
else
(if i.val < 3787 then
6464
else
6465))
else
(if i.val < 3790 then
(if i.val < 3789 then
3143
else
6466)
else
(if i.val < 3791 then
3706
else
6467))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
6250
else
4483)
else
(if i.val < 3795 then
5015
else
6468))
else
(if i.val < 3798 then
(if i.val < 3797 then
5420
else
6271)
else
(if i.val < 3799 then
3489
else
2089)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
6469
else
6470)
else
(if i.val < 3803 then
6471
else
4133))
else
(if i.val < 3806 then
(if i.val < 3805 then
2304
else
6472)
else
(if i.val < 3807 then
4786
else
1455)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
1416
else
5488)
else
(if i.val < 3811 then
5564
else
3228))
else
(if i.val < 3814 then
(if i.val < 3813 then
5617
else
3177)
else
(if i.val < 3815 then
3589
else
5791)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
6473
else
3390)
else
(if i.val < 3819 then
5705
else
5141))
else
(if i.val < 3822 then
(if i.val < 3821 then
1792
else
3150)
else
(if i.val < 3823 then
5411
else
1479))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
6140
else
6141)
else
(if i.val < 3827 then
6142
else
6474))
else
(if i.val < 3830 then
(if i.val < 3829 then
6475
else
4916)
else
(if i.val < 3831 then
6476
else
6477)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
6478
else
6479)
else
(if i.val < 3835 then
3243
else
1722))
else
(if i.val < 3838 then
(if i.val < 3837 then
3149
else
6143)
else
(if i.val < 3839 then
2647
else
6144))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
6145
else
3686)
else
(if i.val < 3843 then
3217
else
5412))
else
(if i.val < 3846 then
(if i.val < 3845 then
2174
else
3648)
else
(if i.val < 3847 then
2442
else
6178)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
6480
else
3287)
else
(if i.val < 3851 then
6481
else
6482))
else
(if i.val < 3854 then
(if i.val < 3853 then
2777
else
6483)
else
(if i.val < 3855 then
3658
else
3649))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
3020
else
3660)
else
(if i.val < 3859 then
6484
else
667))
else
(if i.val < 3862 then
(if i.val < 3861 then
2562
else
6485)
else
(if i.val < 3863 then
6486
else
6487)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
4496
else
6488)
else
(if i.val < 3867 then
6489
else
5916))
else
(if i.val < 3870 then
(if i.val < 3869 then
6490
else
6274)
else
(if i.val < 3871 then
1527
else
3298)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
6491
else
6492)
else
(if i.val < 3875 then
6493
else
3452))
else
(if i.val < 3878 then
(if i.val < 3877 then
1002
else
6494)
else
(if i.val < 3879 then
4259
else
6495)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
5841
else
3724)
else
(if i.val < 3883 then
3743
else
5153))
else
(if i.val < 3886 then
(if i.val < 3885 then
6496
else
3494)
else
(if i.val < 3887 then
6497
else
6498))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
2444
else
6499)
else
(if i.val < 3891 then
4902
else
6500))
else
(if i.val < 3894 then
(if i.val < 3893 then
3496
else
2568)
else
(if i.val < 3895 then
6501
else
6502)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
3608
else
3476)
else
(if i.val < 3899 then
631
else
632))
else
(if i.val < 3902 then
(if i.val < 3901 then
643
else
644)
else
(if i.val < 3903 then
668
else
670))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
671
else
672)
else
(if i.val < 3907 then
673
else
674))
else
(if i.val < 3910 then
(if i.val < 3909 then
675
else
691)
else
(if i.val < 3911 then
692
else
693)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
694
else
695)
else
(if i.val < 3915 then
719
else
721))
else
(if i.val < 3918 then
(if i.val < 3917 then
722
else
723)
else
(if i.val < 3919 then
725
else
778))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
781
else
782)
else
(if i.val < 3923 then
784
else
785))
else
(if i.val < 3926 then
(if i.val < 3925 then
786
else
787)
else
(if i.val < 3927 then
788
else
791)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
792
else
798)
else
(if i.val < 3931 then
799
else
802))
else
(if i.val < 3934 then
(if i.val < 3933 then
803
else
804)
else
(if i.val < 3935 then
906
else
907)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
908
else
909)
else
(if i.val < 3939 then
911
else
912))
else
(if i.val < 3942 then
(if i.val < 3941 then
915
else
918)
else
(if i.val < 3943 then
919
else
924)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
925
else
926)
else
(if i.val < 3947 then
928
else
929))
else
(if i.val < 3950 then
(if i.val < 3949 then
930
else
934)
else
(if i.val < 3951 then
935
else
940))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
941
else
942)
else
(if i.val < 3955 then
943
else
944))
else
(if i.val < 3958 then
(if i.val < 3957 then
945
else
952)
else
(if i.val < 3959 then
953
else
954)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
956
else
958)
else
(if i.val < 3963 then
959
else
960))
else
(if i.val < 3966 then
(if i.val < 3965 then
961
else
963)
else
(if i.val < 3967 then
966
else
968)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
969
else
970)
else
(if i.val < 3971 then
973
else
974))
else
(if i.val < 3974 then
(if i.val < 3973 then
975
else
976)
else
(if i.val < 3975 then
980
else
2980)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
6503
else
6154)
else
(if i.val < 3979 then
6504
else
6505))
else
(if i.val < 3982 then
(if i.val < 3981 then
6246
else
1648)
else
(if i.val < 3983 then
2111
else
6506))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
3616
else
6507)
else
(if i.val < 3987 then
6508
else
6509))
else
(if i.val < 3990 then
(if i.val < 3989 then
6510
else
6511)
else
(if i.val < 3991 then
4481
else
1237)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
6512
else
4748)
else
(if i.val < 3995 then
2177
else
4874))
else
(if i.val < 3998 then
(if i.val < 3997 then
4123
else
1148)
else
(if i.val < 3999 then
4807
else
4749)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
6513
else
5472)
else
(if i.val < 4003 then
6514
else
6515))
else
(if i.val < 4006 then
(if i.val < 4005 then
3719
else
6516)
else
(if i.val < 4007 then
2262
else
3286)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
1544
else
4402)
else
(if i.val < 4011 then
3234
else
6517))
else
(if i.val < 4014 then
(if i.val < 4013 then
6518
else
6519)
else
(if i.val < 4015 then
4094
else
6520))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
3032
else
4955)
else
(if i.val < 4019 then
2051
else
4197))
else
(if i.val < 4022 then
(if i.val < 4021 then
5786
else
6203)
else
(if i.val < 4023 then
6521
else
6522)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
6196
else
6211)
else
(if i.val < 4027 then
3447
else
6523))
else
(if i.val < 4030 then
(if i.val < 4029 then
6524
else
5563)
else
(if i.val < 4031 then
6525
else
6526))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
4765
else
2115)
else
(if i.val < 4035 then
6527
else
4247))
else
(if i.val < 4038 then
(if i.val < 4037 then
3614
else
2784)
else
(if i.val < 4039 then
6528
else
6161)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
1155
else
6529)
else
(if i.val < 4043 then
6530
else
6531))
else
(if i.val < 4046 then
(if i.val < 4045 then
4178
else
4286)
else
(if i.val < 4047 then
4175
else
1244))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
6532
else
6533)
else
(if i.val < 4051 then
6534
else
6535))
else
(if i.val < 4054 then
(if i.val < 4053 then
3348
else
4750)
else
(if i.val < 4055 then
4095
else
6536)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
4764
else
2791)
else
(if i.val < 4059 then
4177
else
6205))
else
(if i.val < 4062 then
(if i.val < 4061 then
6537
else
4272)
else
(if i.val < 4063 then
3603
else
6538)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
2139
else
3207)
else
(if i.val < 4067 then
3602
else
3222))
else
(if i.val < 4070 then
(if i.val < 4069 then
2149
else
5771)
else
(if i.val < 4071 then
6539
else
6540)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
6541
else
2607)
else
(if i.val < 4075 then
6169
else
5596))
else
(if i.val < 4078 then
(if i.val < 4077 then
6542
else
4334)
else
(if i.val < 4079 then
4335
else
4300))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
4371
else
3008)
else
(if i.val < 4083 then
6543
else
3380))
else
(if i.val < 4086 then
(if i.val < 4085 then
6544
else
6040)
else
(if i.val < 4087 then
1166
else
4474)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
3502
else
6545)
else
(if i.val < 4091 then
4817
else
6294))
else
(if i.val < 4094 then
(if i.val < 4093 then
4348
else
3653)
else
(if i.val < 4095 then
2093
else
2163)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0008 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4352 then
(if i.val < 4224 then
(if i.val < 4160 then
(if i.val < 4128 then
(if i.val < 4112 then
(if i.val < 4104 then
(if i.val < 4100 then
(if i.val < 4098 then
(if i.val < 4097 then
4269
else
5929)
else
(if i.val < 4099 then
4836
else
2503))
else
(if i.val < 4102 then
(if i.val < 4101 then
6546
else
4265)
else
(if i.val < 4103 then
1459
else
6135)))
else
(if i.val < 4108 then
(if i.val < 4106 then
(if i.val < 4105 then
6547
else
5944)
else
(if i.val < 4107 then
6548
else
6549))
else
(if i.val < 4110 then
(if i.val < 4109 then
6550
else
6551)
else
(if i.val < 4111 then
6552
else
3636))))
else
(if i.val < 4120 then
(if i.val < 4116 then
(if i.val < 4114 then
(if i.val < 4113 then
1501
else
6553)
else
(if i.val < 4115 then
6554
else
1278))
else
(if i.val < 4118 then
(if i.val < 4117 then
1179
else
6555)
else
(if i.val < 4119 then
6556
else
6557)))
else
(if i.val < 4124 then
(if i.val < 4122 then
(if i.val < 4121 then
6558
else
5005)
else
(if i.val < 4123 then
5718
else
2074))
else
(if i.val < 4126 then
(if i.val < 4125 then
6559
else
6560)
else
(if i.val < 4127 then
6561
else
6562)))))
else
(if i.val < 4144 then
(if i.val < 4136 then
(if i.val < 4132 then
(if i.val < 4130 then
(if i.val < 4129 then
6563
else
4105)
else
(if i.val < 4131 then
1526
else
4455))
else
(if i.val < 4134 then
(if i.val < 4133 then
6564
else
1559)
else
(if i.val < 4135 then
6565
else
6566)))
else
(if i.val < 4140 then
(if i.val < 4138 then
(if i.val < 4137 then
6567
else
2265)
else
(if i.val < 4139 then
6568
else
6569))
else
(if i.val < 4142 then
(if i.val < 4141 then
3268
else
6570)
else
(if i.val < 4143 then
2652
else
6571))))
else
(if i.val < 4152 then
(if i.val < 4148 then
(if i.val < 4146 then
(if i.val < 4145 then
3300
else
6572)
else
(if i.val < 4147 then
6573
else
4864))
else
(if i.val < 4150 then
(if i.val < 4149 then
6574
else
6575)
else
(if i.val < 4151 then
6576
else
3291)))
else
(if i.val < 4156 then
(if i.val < 4154 then
(if i.val < 4153 then
5820
else
5100)
else
(if i.val < 4155 then
5800
else
3001))
else
(if i.val < 4158 then
(if i.val < 4157 then
6577
else
1135)
else
(if i.val < 4159 then
1754
else
6136))))))
else
(if i.val < 4192 then
(if i.val < 4176 then
(if i.val < 4168 then
(if i.val < 4164 then
(if i.val < 4162 then
(if i.val < 4161 then
3205
else
6578)
else
(if i.val < 4163 then
5446
else
4714))
else
(if i.val < 4166 then
(if i.val < 4165 then
6579
else
6580)
else
(if i.val < 4167 then
6581
else
6582)))
else
(if i.val < 4172 then
(if i.val < 4170 then
(if i.val < 4169 then
4285
else
6583)
else
(if i.val < 4171 then
6584
else
6585))
else
(if i.val < 4174 then
(if i.val < 4173 then
6586
else
6587)
else
(if i.val < 4175 then
1539
else
2151))))
else
(if i.val < 4184 then
(if i.val < 4180 then
(if i.val < 4178 then
(if i.val < 4177 then
6588
else
2169)
else
(if i.val < 4179 then
2148
else
6589))
else
(if i.val < 4182 then
(if i.val < 4181 then
5611
else
4762)
else
(if i.val < 4183 then
6590
else
6591)))
else
(if i.val < 4188 then
(if i.val < 4186 then
(if i.val < 4185 then
6592
else
3765)
else
(if i.val < 4187 then
4109
else
6593))
else
(if i.val < 4190 then
(if i.val < 4189 then
6594
else
6595)
else
(if i.val < 4191 then
6596
else
6597)))))
else
(if i.val < 4208 then
(if i.val < 4200 then
(if i.val < 4196 then
(if i.val < 4194 then
(if i.val < 4193 then
5661
else
5948)
else
(if i.val < 4195 then
6598
else
6599))
else
(if i.val < 4198 then
(if i.val < 4197 then
6600
else
2100)
else
(if i.val < 4199 then
2768
else
1519)))
else
(if i.val < 4204 then
(if i.val < 4202 then
(if i.val < 4201 then
2763
else
1477)
else
(if i.val < 4203 then
6601
else
5622))
else
(if i.val < 4206 then
(if i.val < 4205 then
6602
else
6603)
else
(if i.val < 4207 then
1731
else
4240))))
else
(if i.val < 4216 then
(if i.val < 4212 then
(if i.val < 4210 then
(if i.val < 4209 then
6604
else
4284)
else
(if i.val < 4211 then
6225
else
4236))
else
(if i.val < 4214 then
(if i.val < 4213 then
6605
else
6606)
else
(if i.val < 4215 then
6607
else
6608)))
else
(if i.val < 4220 then
(if i.val < 4218 then
(if i.val < 4217 then
4266
else
5931)
else
(if i.val < 4219 then
3206
else
6609))
else
(if i.val < 4222 then
(if i.val < 4221 then
5889
else
3325)
else
(if i.val < 4223 then
6610
else
6195)))))))
else
(if i.val < 4288 then
(if i.val < 4256 then
(if i.val < 4240 then
(if i.val < 4232 then
(if i.val < 4228 then
(if i.val < 4226 then
(if i.val < 4225 then
1029
else
6611)
else
(if i.val < 4227 then
6612
else
1047))
else
(if i.val < 4230 then
(if i.val < 4229 then
6613
else
2806)
else
(if i.val < 4231 then
6614
else
6615)))
else
(if i.val < 4236 then
(if i.val < 4234 then
(if i.val < 4233 then
3699
else
3010)
else
(if i.val < 4235 then
3274
else
3697))
else
(if i.val < 4238 then
(if i.val < 4237 then
3674
else
3259)
else
(if i.val < 4239 then
4841
else
6616))))
else
(if i.val < 4248 then
(if i.val < 4244 then
(if i.val < 4242 then
(if i.val < 4241 then
4340
else
4288)
else
(if i.val < 4243 then
1461
else
6617))
else
(if i.val < 4246 then
(if i.val < 4245 then
6618
else
6619)
else
(if i.val < 4247 then
6620
else
2129)))
else
(if i.val < 4252 then
(if i.val < 4250 then
(if i.val < 4249 then
6621
else
6622)
else
(if i.val < 4251 then
2794
else
6623))
else
(if i.val < 4254 then
(if i.val < 4253 then
6624
else
3245)
else
(if i.val < 4255 then
6625
else
6626)))))
else
(if i.val < 4272 then
(if i.val < 4264 then
(if i.val < 4260 then
(if i.val < 4258 then
(if i.val < 4257 then
6627
else
6628)
else
(if i.val < 4259 then
6629
else
1818))
else
(if i.val < 4262 then
(if i.val < 4261 then
6014
else
6630)
else
(if i.val < 4263 then
5713
else
6202)))
else
(if i.val < 4268 then
(if i.val < 4266 then
(if i.val < 4265 then
6631
else
3665)
else
(if i.val < 4267 then
6165
else
3265))
else
(if i.val < 4270 then
(if i.val < 4269 then
6632
else
6633)
else
(if i.val < 4271 then
4913
else
6634))))
else
(if i.val < 4280 then
(if i.val < 4276 then
(if i.val < 4274 then
(if i.val < 4273 then
2172
else
6635)
else
(if i.val < 4275 then
6636
else
6637))
else
(if i.val < 4278 then
(if i.val < 4277 then
6638
else
6639)
else
(if i.val < 4279 then
6640
else
6641)))
else
(if i.val < 4284 then
(if i.val < 4282 then
(if i.val < 4281 then
6642
else
3669)
else
(if i.val < 4283 then
2773
else
5864))
else
(if i.val < 4286 then
(if i.val < 4285 then
3675
else
3145)
else
(if i.val < 4287 then
2150
else
4122))))))
else
(if i.val < 4320 then
(if i.val < 4304 then
(if i.val < 4296 then
(if i.val < 4292 then
(if i.val < 4290 then
(if i.val < 4289 then
4356
else
6643)
else
(if i.val < 4291 then
6644
else
6857))
else
(if i.val < 4294 then
(if i.val < 4293 then
6925
else
6961)
else
(if i.val < 4295 then
4198
else
7033)))
else
(if i.val < 4300 then
(if i.val < 4298 then
(if i.val < 4297 then
7034
else
7035)
else
(if i.val < 4299 then
2309
else
5813))
else
(if i.val < 4302 then
(if i.val < 4301 then
6655
else
991)
else
(if i.val < 4303 then
2653
else
5452))))
else
(if i.val < 4312 then
(if i.val < 4308 then
(if i.val < 4306 then
(if i.val < 4305 then
1407
else
4372)
else
(if i.val < 4307 then
5633
else
3661))
else
(if i.val < 4310 then
(if i.val < 4309 then
5123
else
2994)
else
(if i.val < 4311 then
1412
else
1427)))
else
(if i.val < 4316 then
(if i.val < 4314 then
(if i.val < 4313 then
5757
else
6854)
else
(if i.val < 4315 then
3181
else
4213))
else
(if i.val < 4318 then
(if i.val < 4317 then
988
else
1806)
else
(if i.val < 4319 then
6839
else
6653)))))
else
(if i.val < 4336 then
(if i.val < 4328 then
(if i.val < 4324 then
(if i.val < 4322 then
(if i.val < 4321 then
4232
else
3362)
else
(if i.val < 4323 then
6858
else
1000))
else
(if i.val < 4326 then
(if i.val < 4325 then
5451
else
6901)
else
(if i.val < 4327 then
6909
else
6910)))
else
(if i.val < 4332 then
(if i.val < 4330 then
(if i.val < 4329 then
6926
else
6927)
else
(if i.val < 4331 then
5733
else
2736))
else
(if i.val < 4334 then
(if i.val < 4333 then
2231
else
5627)
else
(if i.val < 4335 then
4491
else
2191))))
else
(if i.val < 4344 then
(if i.val < 4340 then
(if i.val < 4338 then
(if i.val < 4337 then
1117
else
5170)
else
(if i.val < 4339 then
6962
else
5726))
else
(if i.val < 4342 then
(if i.val < 4341 then
4207
else
7036)
else
(if i.val < 4343 then
7037
else
3164)))
else
(if i.val < 4348 then
(if i.val < 4346 then
(if i.val < 4345 then
5510
else
6054)
else
(if i.val < 4347 then
2299
else
7038))
else
(if i.val < 4350 then
(if i.val < 4349 then
7039
else
7040)
else
(if i.val < 4351 then
7041
else
7042))))))))
else
(if i.val < 4480 then
(if i.val < 4416 then
(if i.val < 4384 then
(if i.val < 4368 then
(if i.val < 4360 then
(if i.val < 4356 then
(if i.val < 4354 then
(if i.val < 4353 then
2807
else
7043)
else
(if i.val < 4355 then
7044
else
7045))
else
(if i.val < 4358 then
(if i.val < 4357 then
4241
else
2473)
else
(if i.val < 4359 then
7046
else
4403)))
else
(if i.val < 4364 then
(if i.val < 4362 then
(if i.val < 4361 then
6937
else
7047)
else
(if i.val < 4363 then
7048
else
6928))
else
(if i.val < 4366 then
(if i.val < 4365 then
7049
else
7050)
else
(if i.val < 4367 then
6912
else
6766))))
else
(if i.val < 4376 then
(if i.val < 4372 then
(if i.val < 4370 then
(if i.val < 4369 then
5449
else
6273)
else
(if i.val < 4371 then
6938
else
6277))
else
(if i.val < 4374 then
(if i.val < 4373 then
6276
else
6239)
else
(if i.val < 4375 then
7051
else
6279)))
else
(if i.val < 4380 then
(if i.val < 4378 then
(if i.val < 4377 then
6267
else
7052)
else
(if i.val < 4379 then
7053
else
7054))
else
(if i.val < 4382 then
(if i.val < 4381 then
7055
else
6923)
else
(if i.val < 4383 then
5936
else
6963)))))
else
(if i.val < 4400 then
(if i.val < 4392 then
(if i.val < 4388 then
(if i.val < 4386 then
(if i.val < 4385 then
5806
else
5782)
else
(if i.val < 4387 then
3718
else
4675))
else
(if i.val < 4390 then
(if i.val < 4389 then
4678
else
5698)
else
(if i.val < 4391 then
6158
else
6964)))
else
(if i.val < 4396 then
(if i.val < 4394 then
(if i.val < 4393 then
3472
else
2601)
else
(if i.val < 4395 then
6965
else
6939))
else
(if i.val < 4398 then
(if i.val < 4397 then
1001
else
6940)
else
(if i.val < 4399 then
6829
else
6941))))
else
(if i.val < 4408 then
(if i.val < 4404 then
(if i.val < 4402 then
(if i.val < 4401 then
5534
else
4226)
else
(if i.val < 4403 then
2087
else
4687))
else
(if i.val < 4406 then
(if i.val < 4405 then
5418
else
7056)
else
(if i.val < 4407 then
7057
else
2643)))
else
(if i.val < 4412 then
(if i.val < 4410 then
(if i.val < 4409 then
5721
else
5628)
else
(if i.val < 4411 then
5917
else
7058))
else
(if i.val < 4414 then
(if i.val < 4413 then
7059
else
2329)
else
(if i.val < 4415 then
4146
else
6261))))))
else
(if i.val < 4448 then
(if i.val < 4432 then
(if i.val < 4424 then
(if i.val < 4420 then
(if i.val < 4418 then
(if i.val < 4417 then
2326
else
4081)
else
(if i.val < 4419 then
7060
else
7061))
else
(if i.val < 4422 then
(if i.val < 4421 then
7062
else
4838)
else
(if i.val < 4423 then
3644
else
1766)))
else
(if i.val < 4428 then
(if i.val < 4426 then
(if i.val < 4425 then
5811
else
2041)
else
(if i.val < 4427 then
2194
else
983))
else
(if i.val < 4430 then
(if i.val < 4429 then
989
else
992)
else
(if i.val < 4431 then
993
else
1027))))
else
(if i.val < 4440 then
(if i.val < 4436 then
(if i.val < 4434 then
(if i.val < 4433 then
1028
else
1030)
else
(if i.val < 4435 then
1031
else
1032))
else
(if i.val < 4438 then
(if i.val < 4437 then
1033
else
1035)
else
(if i.val < 4439 then
2143
else
6966)))
else
(if i.val < 4444 then
(if i.val < 4442 then
(if i.val < 4441 then
6967
else
2047)
else
(if i.val < 4443 then
4861
else
4298))
else
(if i.val < 4446 then
(if i.val < 4445 then
4405
else
6903)
else
(if i.val < 4447 then
6929
else
6930)))))
else
(if i.val < 4464 then
(if i.val < 4456 then
(if i.val < 4452 then
(if i.val < 4450 then
(if i.val < 4449 then
999
else
1009)
else
(if i.val < 4451 then
1010
else
1011))
else
(if i.val < 4454 then
(if i.val < 4453 then
6931
else
6932)
else
(if i.val < 4455 then
2474
else
6933)))
else
(if i.val < 4460 then
(if i.val < 4458 then
(if i.val < 4457 then
2227
else
6934)
else
(if i.val < 4459 then
2229
else
2452))
else
(if i.val < 4462 then
(if i.val < 4461 then
3180
else
6935)
else
(if i.val < 4463 then
6936
else
3623))))
else
(if i.val < 4472 then
(if i.val < 4468 then
(if i.val < 4466 then
(if i.val < 4465 then
5735
else
6950)
else
(if i.val < 4467 then
6968
else
6969))
else
(if i.val < 4470 then
(if i.val < 4469 then
6710
else
6970)
else
(if i.val < 4471 then
2261
else
6971)))
else
(if i.val < 4476 then
(if i.val < 4474 then
(if i.val < 4473 then
6972
else
4668)
else
(if i.val < 4475 then
6973
else
5645))
else
(if i.val < 4478 then
(if i.val < 4477 then
6974
else
4642)
else
(if i.val < 4479 then
6975
else
6976)))))))
else
(if i.val < 4544 then
(if i.val < 4512 then
(if i.val < 4496 then
(if i.val < 4488 then
(if i.val < 4484 then
(if i.val < 4482 then
(if i.val < 4481 then
7010
else
2066)
else
(if i.val < 4483 then
7063
else
1547))
else
(if i.val < 4486 then
(if i.val < 4485 then
5132
else
5684)
else
(if i.val < 4487 then
1143
else
4739)))
else
(if i.val < 4492 then
(if i.val < 4490 then
(if i.val < 4489 then
7064
else
7065)
else
(if i.val < 4491 then
2663
else
4077))
else
(if i.val < 4494 then
(if i.val < 4493 then
7066
else
7067)
else
(if i.val < 4495 then
3065
else
6960))))
else
(if i.val < 4504 then
(if i.val < 4500 then
(if i.val < 4498 then
(if i.val < 4497 then
1790
else
2789)
else
(if i.val < 4499 then
2524
else
7068))
else
(if i.val < 4502 then
(if i.val < 4501 then
7069
else
4497)
else
(if i.val < 4503 then
5686
else
7070)))
else
(if i.val < 4508 then
(if i.val < 4506 then
(if i.val < 4505 then
6820
else
7071)
else
(if i.val < 4507 then
7072
else
5780))
else
(if i.val < 4510 then
(if i.val < 4509 then
7073
else
5694)
else
(if i.val < 4511 then
3301
else
7074)))))
else
(if i.val < 4528 then
(if i.val < 4520 then
(if i.val < 4516 then
(if i.val < 4514 then
(if i.val < 4513 then
4302
else
1392)
else
(if i.val < 4515 then
7075
else
7076))
else
(if i.val < 4518 then
(if i.val < 4517 then
5470
else
7077)
else
(if i.val < 4519 then
7078
else
1386)))
else
(if i.val < 4524 then
(if i.val < 4522 then
(if i.val < 4521 then
7079
else
7080)
else
(if i.val < 4523 then
6685
else
5414))
else
(if i.val < 4526 then
(if i.val < 4525 then
5185
else
4456)
else
(if i.val < 4527 then
4458
else
4332))))
else
(if i.val < 4536 then
(if i.val < 4532 then
(if i.val < 4530 then
(if i.val < 4529 then
6863
else
7081)
else
(if i.val < 4531 then
7082
else
4911))
else
(if i.val < 4534 then
(if i.val < 4533 then
6748
else
6980)
else
(if i.val < 4535 then
6981
else
4974)))
else
(if i.val < 4540 then
(if i.val < 4538 then
(if i.val < 4537 then
6982
else
2192)
else
(if i.val < 4539 then
4690
else
5642))
else
(if i.val < 4542 then
(if i.val < 4541 then
6812
else
4470)
else
(if i.val < 4543 then
7083
else
4636))))))
else
(if i.val < 4576 then
(if i.val < 4560 then
(if i.val < 4552 then
(if i.val < 4548 then
(if i.val < 4546 then
(if i.val < 4545 then
4137
else
4779)
else
(if i.val < 4547 then
7084
else
7085))
else
(if i.val < 4550 then
(if i.val < 4549 then
4730
else
7086)
else
(if i.val < 4551 then
6053
else
7087)))
else
(if i.val < 4556 then
(if i.val < 4554 then
(if i.val < 4553 then
5439
else
1249)
else
(if i.val < 4555 then
4757
else
7088))
else
(if i.val < 4558 then
(if i.val < 4557 then
4416
else
5913)
else
(if i.val < 4559 then
7089
else
4413))))
else
(if i.val < 4568 then
(if i.val < 4564 then
(if i.val < 4562 then
(if i.val < 4561 then
994
else
995)
else
(if i.val < 4563 then
996
else
997))
else
(if i.val < 4566 then
(if i.val < 4565 then
1003
else
1012)
else
(if i.val < 4567 then
1013
else
1036)))
else
(if i.val < 4572 then
(if i.val < 4570 then
(if i.val < 4569 then
1037
else
1038)
else
(if i.val < 4571 then
1039
else
1041))
else
(if i.val < 4574 then
(if i.val < 4573 then
1042
else
1044)
else
(if i.val < 4575 then
1045
else
1046)))))
else
(if i.val < 4592 then
(if i.val < 4584 then
(if i.val < 4580 then
(if i.val < 4578 then
(if i.val < 4577 then
1094
else
1096)
else
(if i.val < 4579 then
1098
else
1100))
else
(if i.val < 4582 then
(if i.val < 4581 then
1101
else
1102)
else
(if i.val < 4583 then
1104
else
1108)))
else
(if i.val < 4588 then
(if i.val < 4586 then
(if i.val < 4585 then
1111
else
1113)
else
(if i.val < 4587 then
1114
else
1115))
else
(if i.val < 4590 then
(if i.val < 4589 then
1116
else
1118)
else
(if i.val < 4591 then
1119
else
1120))))
else
(if i.val < 4600 then
(if i.val < 4596 then
(if i.val < 4594 then
(if i.val < 4593 then
1121
else
1122)
else
(if i.val < 4595 then
6645
else
4784))
else
(if i.val < 4598 then
(if i.val < 4597 then
5635
else
3587)
else
(if i.val < 4599 then
7090
else
7091)))
else
(if i.val < 4604 then
(if i.val < 4602 then
(if i.val < 4601 then
7092
else
5080)
else
(if i.val < 4603 then
2217
else
2656))
else
(if i.val < 4606 then
(if i.val < 4605 then
7093
else
7094)
else
(if i.val < 4607 then
1478
else
4638)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0009 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4864 then
(if i.val < 4736 then
(if i.val < 4672 then
(if i.val < 4640 then
(if i.val < 4624 then
(if i.val < 4616 then
(if i.val < 4612 then
(if i.val < 4610 then
(if i.val < 4609 then
7095
else
6256)
else
(if i.val < 4611 then
3285
else
3167))
else
(if i.val < 4614 then
(if i.val < 4613 then
1491
else
3080)
else
(if i.val < 4615 then
7096
else
6270)))
else
(if i.val < 4620 then
(if i.val < 4618 then
(if i.val < 4617 then
4459
else
7097)
else
(if i.val < 4619 then
7002
else
4683))
else
(if i.val < 4622 then
(if i.val < 4621 then
4679
else
1516)
else
(if i.val < 4623 then
7098
else
7099))))
else
(if i.val < 4632 then
(if i.val < 4628 then
(if i.val < 4626 then
(if i.val < 4625 then
7100
else
7101)
else
(if i.val < 4627 then
4665
else
5776))
else
(if i.val < 4630 then
(if i.val < 4629 then
6269
else
5575)
else
(if i.val < 4631 then
6260
else
4454)))
else
(if i.val < 4636 then
(if i.val < 4634 then
(if i.val < 4633 then
7102
else
1152)
else
(if i.val < 4635 then
4243
else
1261))
else
(if i.val < 4638 then
(if i.val < 4637 then
2264
else
4253)
else
(if i.val < 4639 then
2431
else
7103)))))
else
(if i.val < 4656 then
(if i.val < 4648 then
(if i.val < 4644 then
(if i.val < 4642 then
(if i.val < 4641 then
1156
else
4865)
else
(if i.val < 4643 then
4707
else
4376))
else
(if i.val < 4646 then
(if i.val < 4645 then
7104
else
7105)
else
(if i.val < 4647 then
7106
else
5576)))
else
(if i.val < 4652 then
(if i.val < 4650 then
(if i.val < 4649 then
5691
else
7107)
else
(if i.val < 4651 then
5484
else
5846))
else
(if i.val < 4654 then
(if i.val < 4653 then
7108
else
4732)
else
(if i.val < 4655 then
2669
else
6669))))
else
(if i.val < 4664 then
(if i.val < 4660 then
(if i.val < 4658 then
(if i.val < 4657 then
7109
else
7110)
else
(if i.val < 4659 then
4351
else
7111))
else
(if i.val < 4662 then
(if i.val < 4661 then
7112
else
6170)
else
(if i.val < 4663 then
5849
else
7113)))
else
(if i.val < 4668 then
(if i.val < 4666 then
(if i.val < 4665 then
7114
else
2466)
else
(if i.val < 4667 then
6698
else
5927))
else
(if i.val < 4670 then
(if i.val < 4669 then
2613
else
7115)
else
(if i.val < 4671 then
3482
else
3730))))))
else
(if i.val < 4704 then
(if i.val < 4688 then
(if i.val < 4680 then
(if i.val < 4676 then
(if i.val < 4674 then
(if i.val < 4673 then
3747
else
6234)
else
(if i.val < 4675 then
7116
else
2286))
else
(if i.val < 4678 then
(if i.val < 4677 then
6156
else
5631)
else
(if i.val < 4679 then
2290
else
2460)))
else
(if i.val < 4684 then
(if i.val < 4682 then
(if i.val < 4681 then
7117
else
1170)
else
(if i.val < 4683 then
7118
else
2458))
else
(if i.val < 4686 then
(if i.val < 4685 then
6837
else
6759)
else
(if i.val < 4687 then
7119
else
4359))))
else
(if i.val < 4696 then
(if i.val < 4692 then
(if i.val < 4690 then
(if i.val < 4689 then
4706
else
7120)
else
(if i.val < 4691 then
2258
else
7121))
else
(if i.val < 4694 then
(if i.val < 4693 then
4711
else
6779)
else
(if i.val < 4695 then
4798
else
7122)))
else
(if i.val < 4700 then
(if i.val < 4698 then
(if i.val < 4697 then
7006
else
6233)
else
(if i.val < 4699 then
7123
else
4338))
else
(if i.val < 4702 then
(if i.val < 4701 then
6188
else
4919)
else
(if i.val < 4703 then
3203
else
7124)))))
else
(if i.val < 4720 then
(if i.val < 4712 then
(if i.val < 4708 then
(if i.val < 4706 then
(if i.val < 4705 then
7125
else
6826)
else
(if i.val < 4707 then
7126
else
4477))
else
(if i.val < 4710 then
(if i.val < 4709 then
4475
else
5692)
else
(if i.val < 4711 then
7127
else
7128)))
else
(if i.val < 4716 then
(if i.val < 4714 then
(if i.val < 4713 then
5436
else
2420)
else
(if i.val < 4715 then
7211
else
7419))
else
(if i.val < 4718 then
(if i.val < 4717 then
3515
else
6288)
else
(if i.val < 4719 then
5512
else
4187))))
else
(if i.val < 4728 then
(if i.val < 4724 then
(if i.val < 4722 then
(if i.val < 4721 then
7544
else
7545)
else
(if i.val < 4723 then
4113
else
7546))
else
(if i.val < 4726 then
(if i.val < 4725 then
6151
else
3341)
else
(if i.val < 4727 then
6138
else
4655)))
else
(if i.val < 4732 then
(if i.val < 4730 then
(if i.val < 4729 then
5181
else
7547)
else
(if i.val < 4731 then
2315
else
3497))
else
(if i.val < 4734 then
(if i.val < 4733 then
7548
else
1132)
else
(if i.val < 4735 then
6181
else
4740)))))))
else
(if i.val < 4800 then
(if i.val < 4768 then
(if i.val < 4752 then
(if i.val < 4744 then
(if i.val < 4740 then
(if i.val < 4738 then
(if i.val < 4737 then
6773
else
4751)
else
(if i.val < 4739 then
5001
else
2313))
else
(if i.val < 4742 then
(if i.val < 4741 then
2521
else
6064)
else
(if i.val < 4743 then
2555
else
6700)))
else
(if i.val < 4748 then
(if i.val < 4746 then
(if i.val < 4745 then
5479
else
1180)
else
(if i.val < 4747 then
7359
else
4887))
else
(if i.val < 4750 then
(if i.val < 4749 then
2071
else
2077)
else
(if i.val < 4751 then
2162
else
2491))))
else
(if i.val < 4760 then
(if i.val < 4756 then
(if i.val < 4754 then
(if i.val < 4753 then
2551
else
6753)
else
(if i.val < 4755 then
7313
else
7420))
else
(if i.val < 4758 then
(if i.val < 4757 then
7174
else
2323)
else
(if i.val < 4759 then
6309
else
7549)))
else
(if i.val < 4764 then
(if i.val < 4762 then
(if i.val < 4761 then
6162
else
7231)
else
(if i.val < 4763 then
3471
else
4239))
else
(if i.val < 4766 then
(if i.val < 4765 then
2167
else
2123)
else
(if i.val < 4767 then
7237
else
5546)))))
else
(if i.val < 4784 then
(if i.val < 4776 then
(if i.val < 4772 then
(if i.val < 4770 then
(if i.val < 4769 then
3185
else
3335)
else
(if i.val < 4771 then
7241
else
5541))
else
(if i.val < 4774 then
(if i.val < 4773 then
1141
else
1142)
else
(if i.val < 4775 then
2544
else
2493)))
else
(if i.val < 4780 then
(if i.val < 4778 then
(if i.val < 4777 then
7015
else
6035)
else
(if i.val < 4779 then
1123
else
2310))
else
(if i.val < 4782 then
(if i.val < 4781 then
7200
else
6004)
else
(if i.val < 4783 then
3748
else
3628))))
else
(if i.val < 4792 then
(if i.val < 4788 then
(if i.val < 4786 then
(if i.val < 4785 then
2410
else
4959)
else
(if i.val < 4787 then
1563
else
7243))
else
(if i.val < 4790 then
(if i.val < 4789 then
7244
else
7245)
else
(if i.val < 4791 then
7246
else
5880)))
else
(if i.val < 4796 then
(if i.val < 4794 then
(if i.val < 4793 then
1177
else
6886)
else
(if i.val < 4795 then
6889
else
4877))
else
(if i.val < 4798 then
(if i.val < 4797 then
2649
else
7302)
else
(if i.val < 4799 then
7303
else
6020))))))
else
(if i.val < 4832 then
(if i.val < 4816 then
(if i.val < 4808 then
(if i.val < 4804 then
(if i.val < 4802 then
(if i.val < 4801 then
3474
else
3103)
else
(if i.val < 4803 then
3152
else
2069))
else
(if i.val < 4806 then
(if i.val < 4805 then
7317
else
4992)
else
(if i.val < 4807 then
2581
else
2076)))
else
(if i.val < 4812 then
(if i.val < 4810 then
(if i.val < 4809 then
1284
else
3624)
else
(if i.val < 4811 then
7360
else
3232))
else
(if i.val < 4814 then
(if i.val < 4813 then
7361
else
7362)
else
(if i.val < 4815 then
5149
else
6048))))
else
(if i.val < 4824 then
(if i.val < 4820 then
(if i.val < 4818 then
(if i.val < 4817 then
5823
else
2640)
else
(if i.val < 4819 then
3396
else
6299))
else
(if i.val < 4822 then
(if i.val < 4821 then
6208
else
6167)
else
(if i.val < 4823 then
6719
else
7145)))
else
(if i.val < 4828 then
(if i.val < 4826 then
(if i.val < 4825 then
5766
else
7421)
else
(if i.val < 4827 then
5763
else
7422))
else
(if i.val < 4830 then
(if i.val < 4829 then
7550
else
7551)
else
(if i.val < 4831 then
4248
else
7164)))))
else
(if i.val < 4848 then
(if i.val < 4840 then
(if i.val < 4836 then
(if i.val < 4834 then
(if i.val < 4833 then
6833
else
5461)
else
(if i.val < 4835 then
5117
else
6765))
else
(if i.val < 4838 then
(if i.val < 4837 then
7286
else
4282)
else
(if i.val < 4839 then
2218
else
3278)))
else
(if i.val < 4844 then
(if i.val < 4842 then
(if i.val < 4841 then
1788
else
2739)
else
(if i.val < 4843 then
3525
else
7552))
else
(if i.val < 4846 then
(if i.val < 4845 then
4169
else
2659)
else
(if i.val < 4847 then
7553
else
7554))))
else
(if i.val < 4856 then
(if i.val < 4852 then
(if i.val < 4850 then
(if i.val < 4849 then
7555
else
7556)
else
(if i.val < 4851 then
3768
else
4257))
else
(if i.val < 4854 then
(if i.val < 4853 then
7557
else
2779)
else
(if i.val < 4855 then
7558
else
6758)))
else
(if i.val < 4860 then
(if i.val < 4858 then
(if i.val < 4857 then
6751
else
7559)
else
(if i.val < 4859 then
7560
else
7561))
else
(if i.val < 4862 then
(if i.val < 4861 then
7562
else
2308)
else
(if i.val < 4863 then
7563
else
6254))))))))
else
(if i.val < 4992 then
(if i.val < 4928 then
(if i.val < 4896 then
(if i.val < 4880 then
(if i.val < 4872 then
(if i.val < 4868 then
(if i.val < 4866 then
(if i.val < 4865 then
7469
else
6268)
else
(if i.val < 4867 then
1753
else
7564))
else
(if i.val < 4870 then
(if i.val < 4869 then
5157
else
3695)
else
(if i.val < 4871 then
7363
else
7565)))
else
(if i.val < 4876 then
(if i.val < 4874 then
(if i.val < 4873 then
3475
else
6699)
else
(if i.val < 4875 then
2073
else
4892))
else
(if i.val < 4878 then
(if i.val < 4877 then
5188
else
7520)
else
(if i.val < 4879 then
7566
else
3184))))
else
(if i.val < 4888 then
(if i.val < 4884 then
(if i.val < 4882 then
(if i.val < 4881 then
4410
else
7424)
else
(if i.val < 4883 then
7425
else
5507))
else
(if i.val < 4886 then
(if i.val < 4885 then
6989
else
7392)
else
(if i.val < 4887 then
3087
else
7567)))
else
(if i.val < 4892 then
(if i.val < 4890 then
(if i.val < 4889 then
1178
else
1756)
else
(if i.val < 4891 then
7328
else
5493))
else
(if i.val < 4894 then
(if i.val < 4893 then
7370
else
7371)
else
(if i.val < 4895 then
7372
else
6666)))))
else
(if i.val < 4912 then
(if i.val < 4904 then
(if i.val < 4900 then
(if i.val < 4898 then
(if i.val < 4897 then
7568
else
7569)
else
(if i.val < 4899 then
4460
else
7512))
else
(if i.val < 4902 then
(if i.val < 4901 then
7570
else
1208)
else
(if i.val < 4903 then
1834
else
1171)))
else
(if i.val < 4908 then
(if i.val < 4906 then
(if i.val < 4905 then
4183
else
7340)
else
(if i.val < 4907 then
1460
else
7571))
else
(if i.val < 4910 then
(if i.val < 4909 then
5765
else
7572)
else
(if i.val < 4911 then
3456
else
2240))))
else
(if i.val < 4920 then
(if i.val < 4916 then
(if i.val < 4914 then
(if i.val < 4913 then
7573
else
7574)
else
(if i.val < 4915 then
2587
else
5946))
else
(if i.val < 4918 then
(if i.val < 4917 then
1604
else
5704)
else
(if i.val < 4919 then
5797
else
7575)))
else
(if i.val < 4924 then
(if i.val < 4922 then
(if i.val < 4921 then
7576
else
4703)
else
(if i.val < 4923 then
5693
else
7426))
else
(if i.val < 4926 then
(if i.val < 4925 then
7427
else
7428)
else
(if i.val < 4927 then
5453
else
1146))))))
else
(if i.val < 4960 then
(if i.val < 4944 then
(if i.val < 4936 then
(if i.val < 4932 then
(if i.val < 4930 then
(if i.val < 4929 then
7364
else
5158)
else
(if i.val < 4931 then
1241
else
1242))
else
(if i.val < 4934 then
(if i.val < 4933 then
5513
else
7366)
else
(if i.val < 4935 then
3332
else
7251)))
else
(if i.val < 4940 then
(if i.val < 4938 then
(if i.val < 4937 then
7430
else
3369)
else
(if i.val < 4939 then
7431
else
6672))
else
(if i.val < 4942 then
(if i.val < 4941 then
4331
else
4953)
else
(if i.val < 4943 then
7306
else
6215))))
else
(if i.val < 4952 then
(if i.val < 4948 then
(if i.val < 4946 then
(if i.val < 4945 then
7373
else
1173)
else
(if i.val < 4947 then
1197
else
1198))
else
(if i.val < 4950 then
(if i.val < 4949 then
1199
else
7374)
else
(if i.val < 4951 then
5912
else
5166)))
else
(if i.val < 4956 then
(if i.val < 4954 then
(if i.val < 4953 then
7375
else
2583)
else
(if i.val < 4955 then
5720
else
2098))
else
(if i.val < 4958 then
(if i.val < 4957 then
5169
else
7376)
else
(if i.val < 4959 then
3045
else
5521)))))
else
(if i.val < 4976 then
(if i.val < 4968 then
(if i.val < 4964 then
(if i.val < 4962 then
(if i.val < 4961 then
5523
else
7377)
else
(if i.val < 4963 then
6788
else
7382))
else
(if i.val < 4966 then
(if i.val < 4965 then
7504
else
1487)
else
(if i.val < 4967 then
2760
else
7156)))
else
(if i.val < 4972 then
(if i.val < 4970 then
(if i.val < 4969 then
3461
else
5182)
else
(if i.val < 4971 then
7155
else
2757))
else
(if i.val < 4974 then
(if i.val < 4973 then
7577
else
5011)
else
(if i.val < 4975 then
2255
else
3000))))
else
(if i.val < 4984 then
(if i.val < 4980 then
(if i.val < 4978 then
(if i.val < 4977 then
1266
else
5492)
else
(if i.val < 4979 then
3473
else
7578))
else
(if i.val < 4982 then
(if i.val < 4981 then
4367
else
2812)
else
(if i.val < 4983 then
5525
else
7018)))
else
(if i.val < 4988 then
(if i.val < 4986 then
(if i.val < 4985 then
4283
else
5636)
else
(if i.val < 4987 then
4657
else
4114))
else
(if i.val < 4990 then
(if i.val < 4989 then
7579
else
7580)
else
(if i.val < 4991 then
7432
else
2566)))))))
else
(if i.val < 5056 then
(if i.val < 5024 then
(if i.val < 5008 then
(if i.val < 5000 then
(if i.val < 4996 then
(if i.val < 4994 then
(if i.val < 4993 then
7581
else
6050)
else
(if i.val < 4995 then
2799
else
5863))
else
(if i.val < 4998 then
(if i.val < 4997 then
7582
else
7517)
else
(if i.val < 4999 then
7583
else
1485)))
else
(if i.val < 5004 then
(if i.val < 5002 then
(if i.val < 5001 then
7584
else
7585)
else
(if i.val < 5003 then
4268
else
3761))
else
(if i.val < 5006 then
(if i.val < 5005 then
7586
else
7222)
else
(if i.val < 5007 then
7587
else
7588))))
else
(if i.val < 5016 then
(if i.val < 5012 then
(if i.val < 5010 then
(if i.val < 5009 then
7589
else
4375)
else
(if i.val < 5011 then
7590
else
7390))
else
(if i.val < 5014 then
(if i.val < 5013 then
3630
else
6065)
else
(if i.val < 5015 then
4258
else
1549)))
else
(if i.val < 5020 then
(if i.val < 5018 then
(if i.val < 5017 then
1275
else
7591)
else
(if i.val < 5019 then
6008
else
7247))
else
(if i.val < 5022 then
(if i.val < 5021 then
7423
else
7140)
else
(if i.val < 5023 then
7429
else
3089)))))
else
(if i.val < 5040 then
(if i.val < 5032 then
(if i.val < 5028 then
(if i.val < 5026 then
(if i.val < 5025 then
5655
else
4752)
else
(if i.val < 5027 then
5485
else
1131))
else
(if i.val < 5030 then
(if i.val < 5029 then
1149
else
1150)
else
(if i.val < 5031 then
1154
else
1158)))
else
(if i.val < 5036 then
(if i.val < 5034 then
(if i.val < 5033 then
1243
else
1245)
else
(if i.val < 5035 then
1248
else
1253))
else
(if i.val < 5038 then
(if i.val < 5037 then
1254
else
1255)
else
(if i.val < 5039 then
1256
else
1257))))
else
(if i.val < 5048 then
(if i.val < 5044 then
(if i.val < 5042 then
(if i.val < 5041 then
1258
else
1259)
else
(if i.val < 5043 then
5683
else
5471))
else
(if i.val < 5046 then
(if i.val < 5045 then
7433
else
7434)
else
(if i.val < 5047 then
7435
else
2677)))
else
(if i.val < 5052 then
(if i.val < 5050 then
(if i.val < 5049 then
7436
else
2674)
else
(if i.val < 5051 then
6693
else
7437))
else
(if i.val < 5054 then
(if i.val < 5053 then
6767
else
7438)
else
(if i.val < 5055 then
7136
else
3101))))))
else
(if i.val < 5088 then
(if i.val < 5072 then
(if i.val < 5064 then
(if i.val < 5060 then
(if i.val < 5058 then
(if i.val < 5057 then
4971
else
1565)
else
(if i.val < 5059 then
4966
else
5511))
else
(if i.val < 5062 then
(if i.val < 5061 then
4896
else
7280)
else
(if i.val < 5063 then
2585
else
5703)))
else
(if i.val < 5068 then
(if i.val < 5066 then
(if i.val < 5065 then
7365
else
1181)
else
(if i.val < 5067 then
1182
else
1200))
else
(if i.val < 5070 then
(if i.val < 5069 then
1201
else
1203)
else
(if i.val < 5071 then
4908
else
4876))))
else
(if i.val < 5080 then
(if i.val < 5076 then
(if i.val < 5074 then
(if i.val < 5073 then
2436
else
3102)
else
(if i.val < 5075 then
3096
else
5832))
else
(if i.val < 5078 then
(if i.val < 5077 then
7367
else
4884)
else
(if i.val < 5079 then
7282
else
2810)))
else
(if i.val < 5084 then
(if i.val < 5082 then
(if i.val < 5081 then
2425
else
3606)
else
(if i.val < 5083 then
3064
else
2996))
else
(if i.val < 5086 then
(if i.val < 5085 then
7368
else
3618)
else
(if i.val < 5087 then
6752
else
7369)))))
else
(if i.val < 5104 then
(if i.val < 5096 then
(if i.val < 5092 then
(if i.val < 5090 then
(if i.val < 5089 then
6647
else
7284)
else
(if i.val < 5091 then
7439
else
3111))
else
(if i.val < 5094 then
(if i.val < 5093 then
7440
else
7441)
else
(if i.val < 5095 then
6832
else
7342)))
else
(if i.val < 5100 then
(if i.val < 5098 then
(if i.val < 5097 then
5572
else
3387)
else
(if i.val < 5099 then
6780
else
7442))
else
(if i.val < 5102 then
(if i.val < 5101 then
7443
else
3642)
else
(if i.val < 5103 then
4215
else
1447))))
else
(if i.val < 5112 then
(if i.val < 5108 then
(if i.val < 5106 then
(if i.val < 5105 then
2668
else
6293)
else
(if i.val < 5107 then
6898
else
7444))
else
(if i.val < 5110 then
(if i.val < 5109 then
4249
else
7445)
else
(if i.val < 5111 then
4214
else
2667)))
else
(if i.val < 5116 then
(if i.val < 5114 then
(if i.val < 5113 then
7446
else
2670)
else
(if i.val < 5115 then
1433
else
7447))
else
(if i.val < 5118 then
(if i.val < 5117 then
5428
else
6026)
else
(if i.val < 5119 then
7448
else
7449)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0010 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 5376 then
(if i.val < 5248 then
(if i.val < 5184 then
(if i.val < 5152 then
(if i.val < 5136 then
(if i.val < 5128 then
(if i.val < 5124 then
(if i.val < 5122 then
(if i.val < 5121 then
7450
else
7451)
else
(if i.val < 5123 then
7452
else
3457))
else
(if i.val < 5126 then
(if i.val < 5125 then
5515
else
5514)
else
(if i.val < 5127 then
7453
else
4069)))
else
(if i.val < 5132 then
(if i.val < 5130 then
(if i.val < 5129 then
7505
else
7506)
else
(if i.val < 5131 then
6237
else
6242))
else
(if i.val < 5134 then
(if i.val < 5133 then
7592
else
3516)
else
(if i.val < 5135 then
6243
else
7593))))
else
(if i.val < 5144 then
(if i.val < 5140 then
(if i.val < 5138 then
(if i.val < 5137 then
6223
else
4463)
else
(if i.val < 5139 then
6226
else
6224))
else
(if i.val < 5142 then
(if i.val < 5141 then
7594
else
1585)
else
(if i.val < 5143 then
5840
else
1510)))
else
(if i.val < 5148 then
(if i.val < 5146 then
(if i.val < 5145 then
2557
else
4097)
else
(if i.val < 5147 then
7595
else
7596))
else
(if i.val < 5150 then
(if i.val < 5149 then
7597
else
7598)
else
(if i.val < 5151 then
6747
else
3208)))))
else
(if i.val < 5168 then
(if i.val < 5160 then
(if i.val < 5156 then
(if i.val < 5154 then
(if i.val < 5153 then
4290
else
1826)
else
(if i.val < 5155 then
5621
else
3731))
else
(if i.val < 5158 then
(if i.val < 5157 then
7144
else
2530)
else
(if i.val < 5159 then
2714
else
4812)))
else
(if i.val < 5164 then
(if i.val < 5162 then
(if i.val < 5161 then
6289
else
4231)
else
(if i.val < 5163 then
2795
else
6285))
else
(if i.val < 5166 then
(if i.val < 5165 then
7599
else
7600)
else
(if i.val < 5167 then
2639
else
3157))))
else
(if i.val < 5176 then
(if i.val < 5172 then
(if i.val < 5170 then
(if i.val < 5169 then
6891
else
6315)
else
(if i.val < 5171 then
7601
else
5010))
else
(if i.val < 5174 then
(if i.val < 5173 then
7602
else
5135)
else
(if i.val < 5175 then
3760
else
7603)))
else
(if i.val < 5180 then
(if i.val < 5178 then
(if i.val < 5177 then
7604
else
1512)
else
(if i.val < 5179 then
7405
else
7605))
else
(if i.val < 5182 then
(if i.val < 5181 then
7606
else
3067)
else
(if i.val < 5183 then
7607
else
3211))))))
else
(if i.val < 5216 then
(if i.val < 5200 then
(if i.val < 5192 then
(if i.val < 5188 then
(if i.val < 5186 then
(if i.val < 5185 then
3264
else
2225)
else
(if i.val < 5187 then
7209
else
7399))
else
(if i.val < 5190 then
(if i.val < 5189 then
5071
else
1791)
else
(if i.val < 5191 then
5751
else
5533)))
else
(if i.val < 5196 then
(if i.val < 5194 then
(if i.val < 5193 then
7608
else
7609)
else
(if i.val < 5195 then
2424
else
7610))
else
(if i.val < 5198 then
(if i.val < 5197 then
7611
else
7612)
else
(if i.val < 5199 then
4742
else
7613))))
else
(if i.val < 5208 then
(if i.val < 5204 then
(if i.val < 5202 then
(if i.val < 5201 then
5144
else
7614)
else
(if i.val < 5203 then
1785
else
5743))
else
(if i.val < 5206 then
(if i.val < 5205 then
7138
else
7518)
else
(if i.val < 5207 then
4991
else
3024)))
else
(if i.val < 5212 then
(if i.val < 5210 then
(if i.val < 5209 then
6746
else
5456)
else
(if i.val < 5211 then
5807
else
3179))
else
(if i.val < 5214 then
(if i.val < 5213 then
2475
else
2437)
else
(if i.val < 5215 then
7168
else
7198)))))
else
(if i.val < 5232 then
(if i.val < 5224 then
(if i.val < 5220 then
(if i.val < 5218 then
(if i.val < 5217 then
4806
else
7217)
else
(if i.val < 5219 then
5062
else
4914))
else
(if i.val < 5222 then
(if i.val < 5221 then
7254
else
7013)
else
(if i.val < 5223 then
2769
else
7134)))
else
(if i.val < 5228 then
(if i.val < 5226 then
(if i.val < 5225 then
2498
else
7458)
else
(if i.val < 5227 then
7459
else
3512))
else
(if i.val < 5230 then
(if i.val < 5229 then
7615
else
7616)
else
(if i.val < 5231 then
6182
else
4073))))
else
(if i.val < 5240 then
(if i.val < 5236 then
(if i.val < 5234 then
(if i.val < 5233 then
7617
else
7618)
else
(if i.val < 5235 then
6697
else
2711))
else
(if i.val < 5238 then
(if i.val < 5237 then
7460
else
4407)
else
(if i.val < 5239 then
7461
else
7462)))
else
(if i.val < 5244 then
(if i.val < 5242 then
(if i.val < 5241 then
4796
else
7135)
else
(if i.val < 5243 then
1561
else
3339))
else
(if i.val < 5246 then
(if i.val < 5245 then
7483
else
7619)
else
(if i.val < 5247 then
4845
else
7620)))))))
else
(if i.val < 5312 then
(if i.val < 5280 then
(if i.val < 5264 then
(if i.val < 5256 then
(if i.val < 5252 then
(if i.val < 5250 then
(if i.val < 5249 then
4490
else
7621)
else
(if i.val < 5251 then
5111
else
5104))
else
(if i.val < 5254 then
(if i.val < 5253 then
4654
else
5113)
else
(if i.val < 5255 then
5643
else
4200)))
else
(if i.val < 5260 then
(if i.val < 5258 then
(if i.val < 5257 then
6297
else
6723)
else
(if i.val < 5259 then
7622
else
2542))
else
(if i.val < 5262 then
(if i.val < 5261 then
4853
else
7623)
else
(if i.val < 5263 then
7624
else
5544))))
else
(if i.val < 5272 then
(if i.val < 5268 then
(if i.val < 5266 then
(if i.val < 5265 then
7625
else
4250)
else
(if i.val < 5267 then
5162
else
4994))
else
(if i.val < 5270 then
(if i.val < 5269 then
7626
else
7627)
else
(if i.val < 5271 then
7628
else
6917)))
else
(if i.val < 5276 then
(if i.val < 5274 then
(if i.val < 5273 then
7629
else
4229)
else
(if i.val < 5275 then
4352
else
7630))
else
(if i.val < 5278 then
(if i.val < 5277 then
7631
else
5079)
else
(if i.val < 5279 then
4981
else
1125)))))
else
(if i.val < 5296 then
(if i.val < 5288 then
(if i.val < 5284 then
(if i.val < 5282 then
(if i.val < 5281 then
1126
else
1136)
else
(if i.val < 5283 then
1137
else
1161))
else
(if i.val < 5286 then
(if i.val < 5285 then
1163
else
1164)
else
(if i.val < 5287 then
1165
else
1168)))
else
(if i.val < 5292 then
(if i.val < 5290 then
(if i.val < 5289 then
1183
else
1184)
else
(if i.val < 5291 then
1186
else
1209))
else
(if i.val < 5294 then
(if i.val < 5293 then
1211
else
1212)
else
(if i.val < 5295 then
1213
else
1215))))
else
(if i.val < 5304 then
(if i.val < 5300 then
(if i.val < 5298 then
(if i.val < 5297 then
1268
else
1270)
else
(if i.val < 5299 then
1272
else
1274))
else
(if i.val < 5302 then
(if i.val < 5301 then
1277
else
1283)
else
(if i.val < 5303 then
1286
else
1287)))
else
(if i.val < 5308 then
(if i.val < 5306 then
(if i.val < 5305 then
1288
else
1383)
else
(if i.val < 5307 then
1387
else
1388))
else
(if i.val < 5310 then
(if i.val < 5309 then
1391
else
1394)
else
(if i.val < 5311 then
1400
else
1405))))))
else
(if i.val < 5344 then
(if i.val < 5328 then
(if i.val < 5320 then
(if i.val < 5316 then
(if i.val < 5314 then
(if i.val < 5313 then
1406
else
1410)
else
(if i.val < 5315 then
1411
else
1417))
else
(if i.val < 5318 then
(if i.val < 5317 then
1418
else
1419)
else
(if i.val < 5319 then
1420
else
1421)))
else
(if i.val < 5324 then
(if i.val < 5322 then
(if i.val < 5321 then
1429
else
1430)
else
(if i.val < 5323 then
1432
else
1435))
else
(if i.val < 5326 then
(if i.val < 5325 then
1436
else
1438)
else
(if i.val < 5327 then
1441
else
1443))))
else
(if i.val < 5336 then
(if i.val < 5332 then
(if i.val < 5330 then
(if i.val < 5329 then
1444
else
1445)
else
(if i.val < 5331 then
1448
else
1449))
else
(if i.val < 5334 then
(if i.val < 5333 then
1450
else
1451)
else
(if i.val < 5335 then
7467
else
6768)))
else
(if i.val < 5340 then
(if i.val < 5338 then
(if i.val < 5337 then
2644
else
3046)
else
(if i.val < 5339 then
7632
else
7633))
else
(if i.val < 5342 then
(if i.val < 5341 then
4155
else
6198)
else
(if i.val < 5343 then
7634
else
6291)))))
else
(if i.val < 5360 then
(if i.val < 5352 then
(if i.val < 5348 then
(if i.val < 5346 then
(if i.val < 5345 then
1782
else
2287)
else
(if i.val < 5347 then
7635
else
4233))
else
(if i.val < 5350 then
(if i.val < 5349 then
3099
else
5447)
else
(if i.val < 5351 then
2206
else
6247)))
else
(if i.val < 5356 then
(if i.val < 5354 then
(if i.val < 5353 then
5715
else
6704)
else
(if i.val < 5355 then
1787
else
3124))
else
(if i.val < 5358 then
(if i.val < 5357 then
1639
else
3481)
else
(if i.val < 5359 then
7636
else
7637))))
else
(if i.val < 5368 then
(if i.val < 5364 then
(if i.val < 5362 then
(if i.val < 5361 then
7638
else
5422)
else
(if i.val < 5363 then
6737
else
6943))
else
(if i.val < 5366 then
(if i.val < 5365 then
2990
else
5506)
else
(if i.val < 5367 then
3356
else
6149)))
else
(if i.val < 5372 then
(if i.val < 5370 then
(if i.val < 5369 then
7639
else
6159)
else
(if i.val < 5371 then
7500
else
4958))
else
(if i.val < 5374 then
(if i.val < 5373 then
7640
else
7641)
else
(if i.val < 5375 then
5695
else
5828))))))))
else
(if i.val < 5504 then
(if i.val < 5440 then
(if i.val < 5408 then
(if i.val < 5392 then
(if i.val < 5384 then
(if i.val < 5380 then
(if i.val < 5378 then
(if i.val < 5377 then
7642
else
6853)
else
(if i.val < 5379 then
3050
else
7643))
else
(if i.val < 5382 then
(if i.val < 5381 then
5082
else
4494)
else
(if i.val < 5383 then
7644
else
7470)))
else
(if i.val < 5388 then
(if i.val < 5386 then
(if i.val < 5385 then
2213
else
6734)
else
(if i.val < 5387 then
5489
else
5486))
else
(if i.val < 5390 then
(if i.val < 5389 then
2294
else
7645)
else
(if i.val < 5391 then
7646
else
7647))))
else
(if i.val < 5400 then
(if i.val < 5396 then
(if i.val < 5394 then
(if i.val < 5393 then
4886
else
6845)
else
(if i.val < 5395 then
6852
else
3654))
else
(if i.val < 5398 then
(if i.val < 5397 then
3398
else
5074)
else
(if i.val < 5399 then
7648
else
3072)))
else
(if i.val < 5404 then
(if i.val < 5402 then
(if i.val < 5401 then
5073
else
4801)
else
(if i.val < 5403 then
3077
else
4070))
else
(if i.val < 5406 then
(if i.val < 5405 then
3677
else
7649)
else
(if i.val < 5407 then
7650
else
4379)))))
else
(if i.val < 5424 then
(if i.val < 5416 then
(if i.val < 5412 then
(if i.val < 5410 then
(if i.val < 5409 then
7477
else
3676)
else
(if i.val < 5411 then
7651
else
1594))
else
(if i.val < 5414 then
(if i.val < 5413 then
1654
else
7406)
else
(if i.val < 5415 then
2224
else
1775)))
else
(if i.val < 5420 then
(if i.val < 5418 then
(if i.val < 5417 then
5000
else
7652)
else
(if i.val < 5419 then
6875
else
7529))
else
(if i.val < 5422 then
(if i.val < 5421 then
1551
else
5107)
else
(if i.val < 5423 then
3028
else
1532))))
else
(if i.val < 5432 then
(if i.val < 5428 then
(if i.val < 5426 then
(if i.val < 5425 then
1536
else
7343)
else
(if i.val < 5427 then
6887
else
7653))
else
(if i.val < 5430 then
(if i.val < 5429 then
5550
else
7455)
else
(if i.val < 5431 then
7353
else
7654)))
else
(if i.val < 5436 then
(if i.val < 5434 then
(if i.val < 5433 then
7655
else
7656)
else
(if i.val < 5435 then
3246
else
5096))
else
(if i.val < 5438 then
(if i.val < 5437 then
2516
else
6286)
else
(if i.val < 5439 then
7657
else
2320))))))
else
(if i.val < 5472 then
(if i.val < 5456 then
(if i.val < 5448 then
(if i.val < 5444 then
(if i.val < 5442 then
(if i.val < 5441 then
2234
else
7658)
else
(if i.val < 5443 then
7659
else
7660))
else
(if i.val < 5446 then
(if i.val < 5445 then
7661
else
6957)
else
(if i.val < 5447 then
7264
else
3013)))
else
(if i.val < 5452 then
(if i.val < 5450 then
(if i.val < 5449 then
7662
else
7663)
else
(if i.val < 5451 then
7664
else
7665))
else
(if i.val < 5454 then
(if i.val < 5453 then
7666
else
2541)
else
(if i.val < 5455 then
1735
else
4245))))
else
(if i.val < 5464 then
(if i.val < 5460 then
(if i.val < 5458 then
(if i.val < 5457 then
2571
else
7667)
else
(if i.val < 5459 then
4164
else
7668))
else
(if i.val < 5462 then
(if i.val < 5461 then
7669
else
7670)
else
(if i.val < 5463 then
7671
else
7672)))
else
(if i.val < 5468 then
(if i.val < 5466 then
(if i.val < 5465 then
4848
else
7291)
else
(if i.val < 5467 then
6997
else
3509))
else
(if i.val < 5470 then
(if i.val < 5469 then
4644
else
5809)
else
(if i.val < 5471 then
2196
else
2738)))))
else
(if i.val < 5488 then
(if i.val < 5480 then
(if i.val < 5476 then
(if i.val < 5474 then
(if i.val < 5473 then
2079
else
6732)
else
(if i.val < 5475 then
6729
else
6831))
else
(if i.val < 5478 then
(if i.val < 5477 then
7673
else
4267)
else
(if i.val < 5479 then
6817
else
5562)))
else
(if i.val < 5484 then
(if i.val < 5482 then
(if i.val < 5481 then
7674
else
7675)
else
(if i.val < 5483 then
7676
else
5845))
else
(if i.val < 5486 then
(if i.val < 5485 then
3326
else
2553)
else
(if i.val < 5487 then
3078
else
3306))))
else
(if i.val < 5496 then
(if i.val < 5492 then
(if i.val < 5490 then
(if i.val < 5489 then
1567
else
3076)
else
(if i.val < 5491 then
7677
else
7213))
else
(if i.val < 5494 then
(if i.val < 5493 then
3397
else
7678)
else
(if i.val < 5495 then
7679
else
3394)))
else
(if i.val < 5500 then
(if i.val < 5498 then
(if i.val < 5497 then
3340
else
5433)
else
(if i.val < 5499 then
5856
else
7680))
else
(if i.val < 5502 then
(if i.val < 5501 then
7681
else
7234)
else
(if i.val < 5503 then
7357
else
6760)))))))
else
(if i.val < 5568 then
(if i.val < 5536 then
(if i.val < 5520 then
(if i.val < 5512 then
(if i.val < 5508 then
(if i.val < 5506 then
(if i.val < 5505 then
7682
else
6146)
else
(if i.val < 5507 then
3035
else
2534))
else
(if i.val < 5510 then
(if i.val < 5509 then
4482
else
7683)
else
(if i.val < 5511 then
7221
else
7684)))
else
(if i.val < 5516 then
(if i.val < 5514 then
(if i.val < 5513 then
3480
else
2720)
else
(if i.val < 5515 then
5561
else
5529))
else
(if i.val < 5518 then
(if i.val < 5517 then
3635
else
7685)
else
(if i.val < 5519 then
7686
else
5551))))
else
(if i.val < 5528 then
(if i.val < 5524 then
(if i.val < 5522 then
(if i.val < 5521 then
7345
else
4785)
else
(if i.val < 5523 then
7687
else
7329))
else
(if i.val < 5526 then
(if i.val < 5525 then
4873
else
7688)
else
(if i.val < 5527 then
7493
else
7689)))
else
(if i.val < 5532 then
(if i.val < 5530 then
(if i.val < 5529 then
7690
else
5124)
else
(if i.val < 5531 then
3526
else
7691))
else
(if i.val < 5534 then
(if i.val < 5533 then
1540
else
2481)
else
(if i.val < 5535 then
7692
else
7693)))))
else
(if i.val < 5552 then
(if i.val < 5544 then
(if i.val < 5540 then
(if i.val < 5538 then
(if i.val < 5537 then
7694
else
7695)
else
(if i.val < 5539 then
7696
else
4500))
else
(if i.val < 5542 then
(if i.val < 5541 then
7697
else
7698)
else
(if i.val < 5543 then
7699
else
7700)))
else
(if i.val < 5548 then
(if i.val < 5546 then
(if i.val < 5545 then
2792
else
7394)
else
(if i.val < 5547 then
7701
else
7260))
else
(if i.val < 5550 then
(if i.val < 5549 then
7499
else
7702)
else
(if i.val < 5551 then
5116
else
7474))))
else
(if i.val < 5560 then
(if i.val < 5556 then
(if i.val < 5554 then
(if i.val < 5553 then
4831
else
7703)
else
(if i.val < 5555 then
5833
else
7704))
else
(if i.val < 5558 then
(if i.val < 5557 then
7705
else
7706)
else
(if i.val < 5559 then
7707
else
5120)))
else
(if i.val < 5564 then
(if i.val < 5562 then
(if i.val < 5561 then
7316
else
5125)
else
(if i.val < 5563 then
4744
else
2114))
else
(if i.val < 5566 then
(if i.val < 5565 then
1568
else
7708)
else
(if i.val < 5567 then
6687
else
7861))))))
else
(if i.val < 5600 then
(if i.val < 5584 then
(if i.val < 5576 then
(if i.val < 5572 then
(if i.val < 5570 then
(if i.val < 5569 then
2459
else
7862)
else
(if i.val < 5571 then
3272
else
7824))
else
(if i.val < 5574 then
(if i.val < 5573 then
5435
else
7728)
else
(if i.val < 5575 then
5701
else
2470)))
else
(if i.val < 5580 then
(if i.val < 5578 then
(if i.val < 5577 then
7527
else
6720)
else
(if i.val < 5579 then
4156
else
7296))
else
(if i.val < 5582 then
(if i.val < 5581 then
6754
else
6284)
else
(if i.val < 5583 then
5147
else
8149))))
else
(if i.val < 5592 then
(if i.val < 5588 then
(if i.val < 5586 then
(if i.val < 5585 then
7727
else
7911)
else
(if i.val < 5587 then
7230
else
4488))
else
(if i.val < 5590 then
(if i.val < 5589 then
5688
else
6152)
else
(if i.val < 5591 then
8182
else
5697)))
else
(if i.val < 5596 then
(if i.val < 5594 then
(if i.val < 5593 then
6197
else
7177)
else
(if i.val < 5595 then
4790
else
6232))
else
(if i.val < 5598 then
(if i.val < 5597 then
8101
else
4753)
else
(if i.val < 5599 then
7821
else
4702)))))
else
(if i.val < 5616 then
(if i.val < 5608 then
(if i.val < 5604 then
(if i.val < 5602 then
(if i.val < 5601 then
2554
else
4160)
else
(if i.val < 5603 then
1470
else
7163))
else
(if i.val < 5606 then
(if i.val < 5605 then
5727
else
6042)
else
(if i.val < 5607 then
6024
else
6045)))
else
(if i.val < 5612 then
(if i.val < 5610 then
(if i.val < 5609 then
7026
else
7825)
else
(if i.val < 5611 then
5425
else
7826))
else
(if i.val < 5614 then
(if i.val < 5613 then
3210
else
8052)
else
(if i.val < 5615 then
8053
else
8054))))
else
(if i.val < 5624 then
(if i.val < 5620 then
(if i.val < 5618 then
(if i.val < 5617 then
6186
else
1574)
else
(if i.val < 5619 then
7952
else
5850))
else
(if i.val < 5622 then
(if i.val < 5621 then
6736
else
5878)
else
(if i.val < 5623 then
2559
else
3349)))
else
(if i.val < 5628 then
(if i.val < 5626 then
(if i.val < 5625 then
6001
else
3321)
else
(if i.val < 5627 then
4660
else
7150))
else
(if i.val < 5630 then
(if i.val < 5629 then
2572
else
5547)
else
(if i.val < 5631 then
7238
else
3161)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0011 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 5888 then
(if i.val < 5760 then
(if i.val < 5696 then
(if i.val < 5664 then
(if i.val < 5648 then
(if i.val < 5640 then
(if i.val < 5636 then
(if i.val < 5634 then
(if i.val < 5633 then
7949
else
7948)
else
(if i.val < 5635 then
1482
else
2413))
else
(if i.val < 5638 then
(if i.val < 5637 then
7178
else
6846)
else
(if i.val < 5639 then
7804
else
6201)))
else
(if i.val < 5644 then
(if i.val < 5642 then
(if i.val < 5641 then
5186
else
6308)
else
(if i.val < 5643 then
2259
else
2672))
else
(if i.val < 5646 then
(if i.val < 5645 then
7908
else
4708)
else
(if i.val < 5647 then
3117
else
4780))))
else
(if i.val < 5656 then
(if i.val < 5652 then
(if i.val < 5650 then
(if i.val < 5649 then
5881
else
7850)
else
(if i.val < 5651 then
5699
else
6775))
else
(if i.val < 5654 then
(if i.val < 5653 then
1486
else
1489)
else
(if i.val < 5655 then
4918
else
2550)))
else
(if i.val < 5660 then
(if i.val < 5658 then
(if i.val < 5657 then
7192
else
6036)
else
(if i.val < 5659 then
7197
else
4691))
else
(if i.val < 5662 then
(if i.val < 5661 then
5774
else
6848)
else
(if i.val < 5663 then
6801
else
4754)))))
else
(if i.val < 5680 then
(if i.val < 5672 then
(if i.val < 5668 then
(if i.val < 5666 then
(if i.val < 5665 then
8183
else
4314)
else
(if i.val < 5667 then
1494
else
4879))
else
(if i.val < 5670 then
(if i.val < 5669 then
4770
else
5638)
else
(if i.val < 5671 then
8166
else
7860)))
else
(if i.val < 5676 then
(if i.val < 5674 then
(if i.val < 5673 then
4196
else
6802)
else
(if i.val < 5675 then
4859
else
1505))
else
(if i.val < 5678 then
(if i.val < 5677 then
5151
else
6192)
else
(if i.val < 5679 then
5612
else
5183))))
else
(if i.val < 5688 then
(if i.val < 5684 then
(if i.val < 5682 then
(if i.val < 5681 then
7532
else
1457)
else
(if i.val < 5683 then
1458
else
2737))
else
(if i.val < 5686 then
(if i.val < 5685 then
6221
else
3662)
else
(if i.val < 5687 then
5750
else
4723)))
else
(if i.val < 5692 then
(if i.val < 5690 then
(if i.val < 5689 then
7779
else
4659)
else
(if i.val < 5691 then
5134
else
2762))
else
(if i.val < 5694 then
(if i.val < 5693 then
5993
else
2477)
else
(if i.val < 5695 then
5903
else
3049))))))
else
(if i.val < 5728 then
(if i.val < 5712 then
(if i.val < 5704 then
(if i.val < 5700 then
(if i.val < 5698 then
(if i.val < 5697 then
7822
else
7358)
else
(if i.val < 5699 then
2291
else
7823))
else
(if i.val < 5702 then
(if i.val < 5701 then
5476
else
7863)
else
(if i.val < 5703 then
1737
else
6797)))
else
(if i.val < 5708 then
(if i.val < 5706 then
(if i.val < 5705 then
7864
else
1584)
else
(if i.val < 5707 then
3367
else
3323))
else
(if i.val < 5710 then
(if i.val < 5709 then
4849
else
4968)
else
(if i.val < 5711 then
7299
else
7346))))
else
(if i.val < 5720 then
(if i.val < 5716 then
(if i.val < 5714 then
(if i.val < 5713 then
3261
else
7938)
else
(if i.val < 5715 then
5930
else
3016))
else
(if i.val < 5718 then
(if i.val < 5717 then
3147
else
6827)
else
(if i.val < 5719 then
4287
else
7953)))
else
(if i.val < 5724 then
(if i.val < 5722 then
(if i.val < 5721 then
2552
else
6245)
else
(if i.val < 5723 then
5156
else
7995))
else
(if i.val < 5726 then
(if i.val < 5725 then
4150
else
7996)
else
(if i.val < 5727 then
3253
else
3138)))))
else
(if i.val < 5744 then
(if i.val < 5736 then
(if i.val < 5732 then
(if i.val < 5730 then
(if i.val < 5729 then
7030
else
7888)
else
(if i.val < 5731 then
7889
else
7943))
else
(if i.val < 5734 then
(if i.val < 5733 then
7171
else
7912)
else
(if i.val < 5735 then
7800
else
7161)))
else
(if i.val < 5740 then
(if i.val < 5738 then
(if i.val < 5737 then
7997
else
7780)
else
(if i.val < 5739 then
6794
else
8055))
else
(if i.val < 5742 then
(if i.val < 5741 then
8056
else
7982)
else
(if i.val < 5743 then
5816
else
2563))))
else
(if i.val < 5752 then
(if i.val < 5748 then
(if i.val < 5746 then
(if i.val < 5745 then
3454
else
7137)
else
(if i.val < 5747 then
4476
else
5656))
else
(if i.val < 5750 then
(if i.val < 5749 then
3712
else
5714)
else
(if i.val < 5751 then
4502
else
2480)))
else
(if i.val < 5756 then
(if i.val < 5754 then
(if i.val < 5753 then
7763
else
3711)
else
(if i.val < 5755 then
5553
else
3492))
else
(if i.val < 5758 then
(if i.val < 5757 then
7323
else
8057)
else
(if i.val < 5759 then
8058
else
5730)))))))
else
(if i.val < 5824 then
(if i.val < 5792 then
(if i.val < 5776 then
(if i.val < 5768 then
(if i.val < 5764 then
(if i.val < 5762 then
(if i.val < 5761 then
5937
else
8059)
else
(if i.val < 5763 then
6808
else
7882))
else
(if i.val < 5766 then
(if i.val < 5765 then
3258
else
5070)
else
(if i.val < 5767 then
8060
else
7904)))
else
(if i.val < 5772 then
(if i.val < 5770 then
(if i.val < 5769 then
8017
else
4071)
else
(if i.val < 5771 then
5443
else
5127))
else
(if i.val < 5774 then
(if i.val < 5773 then
7998
else
7941)
else
(if i.val < 5775 then
7961
else
8006))))
else
(if i.val < 5784 then
(if i.val < 5780 then
(if i.val < 5778 then
(if i.val < 5777 then
2467
else
7813)
else
(if i.val < 5779 then
6676
else
8184))
else
(if i.val < 5782 then
(if i.val < 5781 then
7974
else
7402)
else
(if i.val < 5783 then
2208
else
8185)))
else
(if i.val < 5788 then
(if i.val < 5786 then
(if i.val < 5785 then
8070
else
3611)
else
(if i.val < 5787 then
2101
else
8186))
else
(if i.val < 5790 then
(if i.val < 5789 then
6712
else
7141)
else
(if i.val < 5791 then
6044
else
1578)))))
else
(if i.val < 5808 then
(if i.val < 5800 then
(if i.val < 5796 then
(if i.val < 5794 then
(if i.val < 5793 then
5012
else
3466)
else
(if i.val < 5795 then
5017
else
4447))
else
(if i.val < 5798 then
(if i.val < 5797 then
7186
else
5654)
else
(if i.val < 5799 then
7935
else
3714)))
else
(if i.val < 5804 then
(if i.val < 5802 then
(if i.val < 5801 then
8187
else
6741)
else
(if i.val < 5803 then
7933
else
3374))
else
(if i.val < 5806 then
(if i.val < 5805 then
7466
else
8122)
else
(if i.val < 5807 then
2207
else
2573))))
else
(if i.val < 5816 then
(if i.val < 5812 then
(if i.val < 5810 then
(if i.val < 5809 then
7315
else
7203)
else
(if i.val < 5811 then
3681
else
2185))
else
(if i.val < 5814 then
(if i.val < 5813 then
6157
else
7771)
else
(if i.val < 5815 then
5165
else
7967)))
else
(if i.val < 5820 then
(if i.val < 5818 then
(if i.val < 5817 then
7927
else
4457)
else
(if i.val < 5819 then
7976
else
8163))
else
(if i.val < 5822 then
(if i.val < 5821 then
8188
else
5061)
else
(if i.val < 5823 then
4746
else
8189))))))
else
(if i.val < 5856 then
(if i.val < 5840 then
(if i.val < 5832 then
(if i.val < 5828 then
(if i.val < 5826 then
(if i.val < 5825 then
8165
else
5618)
else
(if i.val < 5827 then
8190
else
8050))
else
(if i.val < 5830 then
(if i.val < 5829 then
3052
else
6059)
else
(if i.val < 5831 then
8191
else
8192)))
else
(if i.val < 5836 then
(if i.val < 5834 then
(if i.val < 5833 then
5914
else
5949)
else
(if i.val < 5835 then
8193
else
7766))
else
(if i.val < 5838 then
(if i.val < 5837 then
3094
else
6283)
else
(if i.val < 5839 then
3081
else
5500))))
else
(if i.val < 5848 then
(if i.val < 5844 then
(if i.val < 5842 then
(if i.val < 5841 then
6318
else
1820)
else
(if i.val < 5843 then
3262
else
5460))
else
(if i.val < 5846 then
(if i.val < 5845 then
1591
else
5892)
else
(if i.val < 5847 then
3442
else
3358)))
else
(if i.val < 5852 then
(if i.val < 5850 then
(if i.val < 5849 then
1483
else
3160)
else
(if i.val < 5851 then
6319
else
6046))
else
(if i.val < 5854 then
(if i.val < 5853 then
5076
else
5473)
else
(if i.val < 5855 then
8194
else
3172)))))
else
(if i.val < 5872 then
(if i.val < 5864 then
(if i.val < 5860 then
(if i.val < 5858 then
(if i.val < 5857 then
6834
else
7226)
else
(if i.val < 5859 then
6806
else
5630))
else
(if i.val < 5862 then
(if i.val < 5861 then
7946
else
6919)
else
(if i.val < 5863 then
4343
else
8195)))
else
(if i.val < 5868 then
(if i.val < 5866 then
(if i.val < 5865 then
4984
else
3316)
else
(if i.val < 5867 then
7845
else
8063))
else
(if i.val < 5870 then
(if i.val < 5869 then
8064
else
7803)
else
(if i.val < 5871 then
1764
else
6728))))
else
(if i.val < 5880 then
(if i.val < 5876 then
(if i.val < 5874 then
(if i.val < 5873 then
5522
else
6733)
else
(if i.val < 5875 then
8114
else
6770))
else
(if i.val < 5878 then
(if i.val < 5877 then
7027
else
5940)
else
(if i.val < 5879 then
5154
else
3762)))
else
(if i.val < 5884 then
(if i.val < 5882 then
(if i.val < 5881 then
8048
else
3175)
else
(if i.val < 5883 then
3381
else
6816))
else
(if i.val < 5886 then
(if i.val < 5885 then
8181
else
5064)
else
(if i.val < 5887 then
1590
else
7285))))))))
else
(if i.val < 6016 then
(if i.val < 5952 then
(if i.val < 5920 then
(if i.val < 5904 then
(if i.val < 5896 then
(if i.val < 5892 then
(if i.val < 5890 then
(if i.val < 5889 then
5847
else
3449)
else
(if i.val < 5891 then
4263
else
6749))
else
(if i.val < 5894 then
(if i.val < 5893 then
5483
else
1769)
else
(if i.val < 5895 then
4680
else
5999)))
else
(if i.val < 5900 then
(if i.val < 5898 then
(if i.val < 5897 then
5891
else
3775)
else
(if i.val < 5899 then
3717
else
7165))
else
(if i.val < 5902 then
(if i.val < 5901 then
8009
else
5494)
else
(if i.val < 5903 then
4144
else
4509))))
else
(if i.val < 5912 then
(if i.val < 5908 then
(if i.val < 5906 then
(if i.val < 5905 then
8146
else
5138)
else
(if i.val < 5907 then
3440
else
8196))
else
(if i.val < 5910 then
(if i.val < 5909 then
8197
else
8198)
else
(if i.val < 5911 then
8199
else
6229)))
else
(if i.val < 5916 then
(if i.val < 5914 then
(if i.val < 5913 then
2636
else
2327)
else
(if i.val < 5915 then
5075
else
6707))
else
(if i.val < 5918 then
(if i.val < 5917 then
1799
else
4880)
else
(if i.val < 5919 then
5088
else
7979)))))
else
(if i.val < 5936 then
(if i.val < 5928 then
(if i.val < 5924 then
(if i.val < 5922 then
(if i.val < 5921 then
7384
else
7753)
else
(if i.val < 5923 then
8022
else
6179))
else
(if i.val < 5926 then
(if i.val < 5925 then
7202
else
6717)
else
(if i.val < 5927 then
8083
else
8200)))
else
(if i.val < 5932 then
(if i.val < 5930 then
(if i.val < 5929 then
5516
else
5145)
else
(if i.val < 5931 then
5749
else
8105))
else
(if i.val < 5934 then
(if i.val < 5933 then
8201
else
8202)
else
(if i.val < 5935 then
4167
else
5466))))
else
(if i.val < 5944 then
(if i.val < 5940 then
(if i.val < 5938 then
(if i.val < 5937 then
7733
else
6781)
else
(if i.val < 5939 then
8023
else
8203))
else
(if i.val < 5942 then
(if i.val < 5941 then
8204
else
1608)
else
(if i.val < 5943 then
7985
else
6180)))
else
(if i.val < 5948 then
(if i.val < 5946 then
(if i.val < 5945 then
4129
else
4894)
else
(if i.val < 5947 then
2610
else
7839))
else
(if i.val < 5950 then
(if i.val < 5949 then
6894
else
5554)
else
(if i.val < 5951 then
5555
else
5716))))))
else
(if i.val < 5984 then
(if i.val < 5968 then
(if i.val < 5960 then
(if i.val < 5956 then
(if i.val < 5954 then
(if i.val < 5953 then
8065
else
4811)
else
(if i.val < 5955 then
7758
else
2216))
else
(if i.val < 5958 then
(if i.val < 5957 then
3736
else
1612)
else
(if i.val < 5959 then
1514
else
1723)))
else
(if i.val < 5964 then
(if i.val < 5962 then
(if i.val < 5961 then
1724
else
7999)
else
(if i.val < 5963 then
8000
else
6252))
else
(if i.val < 5966 then
(if i.val < 5965 then
1732
else
1734)
else
(if i.val < 5967 then
8004
else
8005))))
else
(if i.val < 5976 then
(if i.val < 5972 then
(if i.val < 5970 then
(if i.val < 5969 then
3297
else
5785)
else
(if i.val < 5971 then
8031
else
3090))
else
(if i.val < 5974 then
(if i.val < 5973 then
6822
else
2212)
else
(if i.val < 5975 then
1658
else
4809)))
else
(if i.val < 5980 then
(if i.val < 5978 then
(if i.val < 5977 then
4221
else
3327)
else
(if i.val < 5979 then
8010
else
8011))
else
(if i.val < 5982 then
(if i.val < 5981 then
1592
else
1593)
else
(if i.val < 5983 then
1636
else
1637)))))
else
(if i.val < 6000 then
(if i.val < 5992 then
(if i.val < 5988 then
(if i.val < 5986 then
(if i.val < 5985 then
1638
else
5906)
else
(if i.val < 5987 then
1538
else
8012))
else
(if i.val < 5990 then
(if i.val < 5989 then
2107
else
3771)
else
(if i.val < 5991 then
8013
else
6879)))
else
(if i.val < 5996 then
(if i.val < 5994 then
(if i.val < 5993 then
4100
else
4709)
else
(if i.val < 5995 then
7502
else
4089))
else
(if i.val < 5998 then
(if i.val < 5997 then
7212
else
7970)
else
(if i.val < 5999 then
8020
else
8205))))
else
(if i.val < 6008 then
(if i.val < 6004 then
(if i.val < 6002 then
(if i.val < 6001 then
6313
else
3252)
else
(if i.val < 6003 then
3664
else
7740))
else
(if i.val < 6006 then
(if i.val < 6005 then
8021
else
7866)
else
(if i.val < 6007 then
6052
else
6314)))
else
(if i.val < 6012 then
(if i.val < 6010 then
(if i.val < 6009 then
6888
else
3467)
else
(if i.val < 6011 then
6005
else
6750))
else
(if i.val < 6014 then
(if i.val < 6013 then
7875
else
4957)
else
(if i.val < 6015 then
8086
else
1763)))))))
else
(if i.val < 6080 then
(if i.val < 6048 then
(if i.val < 6032 then
(if i.val < 6024 then
(if i.val < 6020 then
(if i.val < 6018 then
(if i.val < 6017 then
5091
else
6745)
else
(if i.val < 6019 then
4900
else
8032))
else
(if i.val < 6022 then
(if i.val < 6021 then
8206
else
8207)
else
(if i.val < 6023 then
5897
else
7508)))
else
(if i.val < 6028 then
(if i.val < 6026 then
(if i.val < 6025 then
7478
else
6177)
else
(if i.val < 6027 then
4834
else
8208))
else
(if i.val < 6030 then
(if i.val < 6029 then
4671
else
6194)
else
(if i.val < 6031 then
4111
else
3302))))
else
(if i.val < 6040 then
(if i.val < 6036 then
(if i.val < 6034 then
(if i.val < 6033 then
7928
else
8139)
else
(if i.val < 6035 then
8209
else
2527))
else
(if i.val < 6038 then
(if i.val < 6037 then
8103
else
4170)
else
(if i.val < 6039 then
4256
else
8178)))
else
(if i.val < 6044 then
(if i.val < 6042 then
(if i.val < 6041 then
7883
else
7983)
else
(if i.val < 6043 then
8210
else
8127))
else
(if i.val < 6046 then
(if i.val < 6045 then
3702
else
8211)
else
(if i.val < 6047 then
6139
else
8164)))))
else
(if i.val < 6064 then
(if i.val < 6056 then
(if i.val < 6052 then
(if i.val < 6050 then
(if i.val < 6049 then
8212
else
6836)
else
(if i.val < 6051 then
8213
else
4328))
else
(if i.val < 6054 then
(if i.val < 6053 then
6230
else
2317)
else
(if i.val < 6055 then
2765
else
6025)))
else
(if i.val < 6060 then
(if i.val < 6058 then
(if i.val < 6057 then
8214
else
8215)
else
(if i.val < 6059 then
8216
else
7852))
else
(if i.val < 6062 then
(if i.val < 6061 then
6280
else
3524)
else
(if i.val < 6063 then
4422
else
1807))))
else
(if i.val < 6072 then
(if i.val < 6068 then
(if i.val < 6066 then
(if i.val < 6065 then
2747
else
8217)
else
(if i.val < 6067 then
6994
else
1767))
else
(if i.val < 6070 then
(if i.val < 6069 then
5167
else
8061)
else
(if i.val < 6071 then
8062
else
8066)))
else
(if i.val < 6076 then
(if i.val < 6074 then
(if i.val < 6073 then
8067
else
6206)
else
(if i.val < 6075 then
5434
else
8068))
else
(if i.val < 6078 then
(if i.val < 6077 then
2197
else
8069)
else
(if i.val < 6079 then
7378
else
7782))))))
else
(if i.val < 6112 then
(if i.val < 6096 then
(if i.val < 6088 then
(if i.val < 6084 then
(if i.val < 6082 then
(if i.val < 6081 then
5764
else
4237)
else
(if i.val < 6083 then
1476
else
1484))
else
(if i.val < 6086 then
(if i.val < 6085 then
1517
else
1518)
else
(if i.val < 6087 then
1520
else
1521)))
else
(if i.val < 6092 then
(if i.val < 6090 then
(if i.val < 6089 then
1522
else
1523)
else
(if i.val < 6091 then
1531
else
1533))
else
(if i.val < 6094 then
(if i.val < 6093 then
1534
else
1738)
else
(if i.val < 6095 then
1744
else
1745))))
else
(if i.val < 6104 then
(if i.val < 6100 then
(if i.val < 6098 then
(if i.val < 6097 then
1746
else
1748)
else
(if i.val < 6099 then
1749
else
1757))
else
(if i.val < 6102 then
(if i.val < 6101 then
1758
else
1759)
else
(if i.val < 6103 then
1760
else
1761)))
else
(if i.val < 6108 then
(if i.val < 6106 then
(if i.val < 6105 then
1765
else
1771)
else
(if i.val < 6107 then
1772
else
1773))
else
(if i.val < 6110 then
(if i.val < 6109 then
4783
else
6724)
else
(if i.val < 6111 then
7331
else
8071)))))
else
(if i.val < 6128 then
(if i.val < 6120 then
(if i.val < 6116 then
(if i.val < 6114 then
(if i.val < 6113 then
6735
else
7986)
else
(if i.val < 6115 then
8072
else
8073))
else
(if i.val < 6118 then
(if i.val < 6117 then
3142
else
5101)
else
(if i.val < 6119 then
8074
else
8075)))
else
(if i.val < 6124 then
(if i.val < 6122 then
(if i.val < 6121 then
4093
else
7942)
else
(if i.val < 6123 then
6809
else
8076))
else
(if i.val < 6126 then
(if i.val < 6125 then
5685
else
6002)
else
(if i.val < 6127 then
7714
else
2159))))
else
(if i.val < 6136 then
(if i.val < 6132 then
(if i.val < 6130 then
(if i.val < 6129 then
4281
else
1668)
else
(if i.val < 6131 then
1462
else
5409))
else
(if i.val < 6134 then
(if i.val < 6133 then
7954
else
4489)
else
(if i.val < 6135 then
8001
else
8002)))
else
(if i.val < 6140 then
(if i.val < 6138 then
(if i.val < 6137 then
8003
else
3766)
else
(if i.val < 6139 then
7528
else
5851))
else
(if i.val < 6142 then
(if i.val < 6141 then
1596
else
1597)
else
(if i.val < 6143 then
1600
else
1646)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0012 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 6400 then
(if i.val < 6272 then
(if i.val < 6208 then
(if i.val < 6176 then
(if i.val < 6160 then
(if i.val < 6152 then
(if i.val < 6148 then
(if i.val < 6146 then
(if i.val < 6145 then
1649
else
1650)
else
(if i.val < 6147 then
6815
else
4275))
else
(if i.val < 6150 then
(if i.val < 6149 then
6843
else
3037)
else
(if i.val < 6151 then
4289
else
7909)))
else
(if i.val < 6156 then
(if i.val < 6154 then
(if i.val < 6153 then
3774
else
3750)
else
(if i.val < 6155 then
2040
else
7981))
else
(if i.val < 6158 then
(if i.val < 6157 then
3178
else
8007)
else
(if i.val < 6159 then
2292
else
3041))))
else
(if i.val < 6168 then
(if i.val < 6164 then
(if i.val < 6162 then
(if i.val < 6161 then
3073
else
2136)
else
(if i.val < 6163 then
2505
else
7153))
else
(if i.val < 6166 then
(if i.val < 6165 then
4179
else
4216)
else
(if i.val < 6167 then
4639
else
8008)))
else
(if i.val < 6172 then
(if i.val < 6170 then
(if i.val < 6169 then
8029
else
8033)
else
(if i.val < 6171 then
3444
else
5115))
else
(if i.val < 6174 then
(if i.val < 6173 then
3500
else
7130)
else
(if i.val < 6175 then
8077
else
5586)))))
else
(if i.val < 6192 then
(if i.val < 6184 then
(if i.val < 6180 then
(if i.val < 6178 then
(if i.val < 6177 then
7201
else
6055)
else
(if i.val < 6179 then
1662
else
3377))
else
(if i.val < 6182 then
(if i.val < 6181 then
7354
else
2520)
else
(if i.val < 6183 then
2606
else
8078)))
else
(if i.val < 6188 then
(if i.val < 6186 then
(if i.val < 6185 then
8079
else
8080)
else
(if i.val < 6187 then
8081
else
4721))
else
(if i.val < 6190 then
(if i.val < 6189 then
3176
else
7915)
else
(if i.val < 6191 then
3508
else
8047))))
else
(if i.val < 6200 then
(if i.val < 6196 then
(if i.val < 6194 then
(if i.val < 6193 then
3209
else
8082)
else
(if i.val < 6195 then
7724
else
7819))
else
(if i.val < 6198 then
(if i.val < 6197 then
2106
else
8084)
else
(if i.val < 6199 then
3002
else
8085)))
else
(if i.val < 6204 then
(if i.val < 6202 then
(if i.val < 6201 then
6021
else
6783)
else
(if i.val < 6203 then
5890
else
2102))
else
(if i.val < 6206 then
(if i.val < 6205 then
4184
else
2170)
else
(if i.val < 6207 then
3244
else
8087))))))
else
(if i.val < 6240 then
(if i.val < 6224 then
(if i.val < 6216 then
(if i.val < 6212 then
(if i.val < 6210 then
(if i.val < 6209 then
3739
else
8088)
else
(if i.val < 6211 then
6895
else
2108))
else
(if i.val < 6214 then
(if i.val < 6213 then
7905
else
4828)
else
(if i.val < 6215 then
5404
else
2595)))
else
(if i.val < 6220 then
(if i.val < 6218 then
(if i.val < 6217 then
4910
else
4978)
else
(if i.val < 6219 then
8135
else
1781))
else
(if i.val < 6222 then
(if i.val < 6221 then
8218
else
4485)
else
(if i.val < 6223 then
8037
else
8219))))
else
(if i.val < 6232 then
(if i.val < 6228 then
(if i.val < 6226 then
(if i.val < 6225 then
6902
else
8220)
else
(if i.val < 6227 then
5905
else
6804))
else
(if i.val < 6230 then
(if i.val < 6229 then
7389
else
6648)
else
(if i.val < 6231 then
6006
else
7761)))
else
(if i.val < 6236 then
(if i.val < 6234 then
(if i.val < 6233 then
6856
else
8221)
else
(if i.val < 6235 then
7297
else
2797))
else
(if i.val < 6238 then
(if i.val < 6237 then
8094
else
7870)
else
(if i.val < 6239 then
8147
else
8222)))))
else
(if i.val < 6256 then
(if i.val < 6248 then
(if i.val < 6244 then
(if i.val < 6242 then
(if i.val < 6241 then
6835
else
5673)
else
(if i.val < 6243 then
7288
else
5690))
else
(if i.val < 6246 then
(if i.val < 6245 then
7004
else
4408)
else
(if i.val < 6247 then
2045
else
3015)))
else
(if i.val < 6252 then
(if i.val < 6250 then
(if i.val < 6249 then
5824
else
7734)
else
(if i.val < 6251 then
1546
else
1795))
else
(if i.val < 6254 then
(if i.val < 6253 then
3592
else
4138)
else
(if i.val < 6255 then
3168
else
7929))))
else
(if i.val < 6264 then
(if i.val < 6260 then
(if i.val < 6258 then
(if i.val < 6257 then
2439
else
3290)
else
(if i.val < 6259 then
8157
else
8158))
else
(if i.val < 6262 then
(if i.val < 6261 then
2471
else
8223)
else
(if i.val < 6263 then
3305
else
3289)))
else
(if i.val < 6268 then
(if i.val < 6266 then
(if i.val < 6265 then
7926
else
1836)
else
(if i.val < 6267 then
7503
else
4643))
else
(if i.val < 6270 then
(if i.val < 6269 then
4641
else
2468)
else
(if i.val < 6271 then
2451
else
1552)))))))
else
(if i.val < 6336 then
(if i.val < 6304 then
(if i.val < 6288 then
(if i.val < 6280 then
(if i.val < 6276 then
(if i.val < 6274 then
(if i.val < 6273 then
7785
else
8156)
else
(if i.val < 6275 then
1801
else
3296))
else
(if i.val < 6278 then
(if i.val < 6277 then
4305
else
4080)
else
(if i.val < 6279 then
3115
else
5009)))
else
(if i.val < 6284 then
(if i.val < 6282 then
(if i.val < 6281 then
3518
else
3216)
else
(if i.val < 6283 then
7831
else
3218))
else
(if i.val < 6286 then
(if i.val < 6285 then
8025
else
8137)
else
(if i.val < 6287 then
3746
else
3740))))
else
(if i.val < 6296 then
(if i.val < 6292 then
(if i.val < 6290 then
(if i.val < 6289 then
3269
else
7788)
else
(if i.val < 6291 then
8024
else
3004))
else
(if i.val < 6294 then
(if i.val < 6293 then
5480
else
3123)
else
(if i.val < 6295 then
7543
else
7514)))
else
(if i.val < 6300 then
(if i.val < 6298 then
(if i.val < 6297 then
8224
else
2771)
else
(if i.val < 6299 then
3131
else
7147))
else
(if i.val < 6302 then
(if i.val < 6301 then
8225
else
4979)
else
(if i.val < 6303 then
4084
else
6862)))))
else
(if i.val < 6320 then
(if i.val < 6312 then
(if i.val < 6308 then
(if i.val < 6306 then
(if i.val < 6305 then
4280
else
8116)
else
(if i.val < 6307 then
7298
else
8226))
else
(if i.val < 6310 then
(if i.val < 6309 then
7196
else
7833)
else
(if i.val < 6311 then
4856
else
5778)))
else
(if i.val < 6316 then
(if i.val < 6314 then
(if i.val < 6313 then
7300
else
7350)
else
(if i.val < 6315 then
8169
else
4956))
else
(if i.val < 6318 then
(if i.val < 6317 then
7725
else
3745)
else
(if i.val < 6319 then
5142
else
5619))))
else
(if i.val < 6328 then
(if i.val < 6324 then
(if i.val < 6322 then
(if i.val < 6321 then
6706
else
6884)
else
(if i.val < 6323 then
6278
else
2116))
else
(if i.val < 6326 then
(if i.val < 6325 then
5646
else
7524)
else
(if i.val < 6327 then
7289
else
2046)))
else
(if i.val < 6332 then
(if i.val < 6330 then
(if i.val < 6329 then
6660
else
3018)
else
(if i.val < 6331 then
6298
else
7742))
else
(if i.val < 6334 then
(if i.val < 6333 then
5855
else
4768)
else
(if i.val < 6335 then
7848
else
5712))))))
else
(if i.val < 6368 then
(if i.val < 6352 then
(if i.val < 6344 then
(if i.val < 6340 then
(if i.val < 6338 then
(if i.val < 6337 then
2457
else
5184)
else
(if i.val < 6339 then
2325
else
4140))
else
(if i.val < 6342 then
(if i.val < 6341 then
2119
else
8153)
else
(if i.val < 6343 then
4234
else
4839)))
else
(if i.val < 6348 then
(if i.val < 6346 then
(if i.val < 6345 then
6864
else
8227)
else
(if i.val < 6347 then
8228
else
8161))
else
(if i.val < 6350 then
(if i.val < 6349 then
6263
else
6257)
else
(if i.val < 6351 then
4151
else
8229))))
else
(if i.val < 6360 then
(if i.val < 6356 then
(if i.val < 6354 then
(if i.val < 6353 then
6275
else
6686)
else
(if i.val < 6355 then
4510
else
6031))
else
(if i.val < 6358 then
(if i.val < 6357 then
6999
else
6262)
else
(if i.val < 6359 then
5487
else
7772)))
else
(if i.val < 6364 then
(if i.val < 6362 then
(if i.val < 6361 then
7950
else
7139)
else
(if i.val < 6363 then
8230
else
7021))
else
(if i.val < 6366 then
(if i.val < 6365 then
3040
else
7464)
else
(if i.val < 6367 then
7509
else
5625)))))
else
(if i.val < 6384 then
(if i.val < 6376 then
(if i.val < 6372 then
(if i.val < 6370 then
(if i.val < 6369 then
5707
else
8092)
else
(if i.val < 6371 then
4769
else
8231))
else
(if i.val < 6374 then
(if i.val < 6373 then
5496
else
4725)
else
(if i.val < 6375 then
3229
else
3148)))
else
(if i.val < 6380 then
(if i.val < 6378 then
(if i.val < 6377 then
7711
else
3586)
else
(if i.val < 6379 then
5706
else
8093))
else
(if i.val < 6382 then
(if i.val < 6381 then
8095
else
7977)
else
(if i.val < 6383 then
8232
else
4083))))
else
(if i.val < 6392 then
(if i.val < 6388 then
(if i.val < 6386 then
(if i.val < 6385 then
5882
else
3599)
else
(if i.val < 6387 then
8233
else
7712))
else
(if i.val < 6390 then
(if i.val < 6389 then
8117
else
5097)
else
(if i.val < 6391 then
8234
else
2981)))
else
(if i.val < 6396 then
(if i.val < 6394 then
(if i.val < 6393 then
8235
else
5495)
else
(if i.val < 6395 then
3093
else
4818))
else
(if i.val < 6398 then
(if i.val < 6397 then
5744
else
8096)
else
(if i.val < 6399 then
5793
else
4800))))))))
else
(if i.val < 6528 then
(if i.val < 6464 then
(if i.val < 6432 then
(if i.val < 6416 then
(if i.val < 6408 then
(if i.val < 6404 then
(if i.val < 6402 then
(if i.val < 6401 then
4670
else
3484)
else
(if i.val < 6403 then
6810
else
2060))
else
(if i.val < 6406 then
(if i.val < 6405 then
3227
else
5755)
else
(if i.val < 6407 then
4731
else
6172)))
else
(if i.val < 6412 then
(if i.val < 6410 then
(if i.val < 6409 then
4088
else
3137)
else
(if i.val < 6411 then
7971
else
6805))
else
(if i.val < 6414 then
(if i.val < 6413 then
6778
else
6190)
else
(if i.val < 6415 then
5467
else
1828))))
else
(if i.val < 6424 then
(if i.val < 6420 then
(if i.val < 6418 then
(if i.val < 6417 then
3754
else
5133)
else
(if i.val < 6419 then
8236
else
7980))
else
(if i.val < 6422 then
(if i.val < 6421 then
6061
else
4842)
else
(if i.val < 6423 then
8237
else
5810)))
else
(if i.val < 6428 then
(if i.val < 6426 then
(if i.val < 6425 then
2770
else
7925)
else
(if i.val < 6427 then
3759
else
8142))
else
(if i.val < 6430 then
(if i.val < 6429 then
2236
else
4869)
else
(if i.val < 6431 then
2764
else
8238)))))
else
(if i.val < 6448 then
(if i.val < 6440 then
(if i.val < 6436 then
(if i.val < 6434 then
(if i.val < 6433 then
8162
else
5753)
else
(if i.val < 6435 then
5748
else
3240))
else
(if i.val < 6438 then
(if i.val < 6437 then
5799
else
2502)
else
(if i.val < 6439 then
5898
else
3125)))
else
(if i.val < 6444 then
(if i.val < 6442 then
(if i.val < 6441 then
8239
else
2235)
else
(if i.val < 6443 then
5155
else
2237))
else
(if i.val < 6446 then
(if i.val < 6445 then
6317
else
4672)
else
(if i.val < 6447 then
4782
else
6153))))
else
(if i.val < 6456 then
(if i.val < 6452 then
(if i.val < 6450 then
(if i.val < 6449 then
3445
else
2546)
else
(if i.val < 6451 then
3700
else
8240))
else
(if i.val < 6454 then
(if i.val < 6453 then
8241
else
5174)
else
(if i.val < 6455 then
5003
else
5879)))
else
(if i.val < 6460 then
(if i.val < 6458 then
(if i.val < 6457 then
4185
else
6137)
else
(if i.val < 6459 then
4850
else
3463))
else
(if i.val < 6462 then
(if i.val < 6461 then
1463
else
1464)
else
(if i.val < 6463 then
1492
else
1493))))))
else
(if i.val < 6496 then
(if i.val < 6480 then
(if i.val < 6472 then
(if i.val < 6468 then
(if i.val < 6466 then
(if i.val < 6465 then
1495
else
1496)
else
(if i.val < 6467 then
1542
else
1545))
else
(if i.val < 6470 then
(if i.val < 6469 then
1550
else
1555)
else
(if i.val < 6471 then
1556
else
1557)))
else
(if i.val < 6476 then
(if i.val < 6474 then
(if i.val < 6473 then
1562
else
1579)
else
(if i.val < 6475 then
1601
else
1603))
else
(if i.val < 6478 then
(if i.val < 6477 then
1605
else
1606)
else
(if i.val < 6479 then
1607
else
1609))))
else
(if i.val < 6488 then
(if i.val < 6484 then
(if i.val < 6482 then
(if i.val < 6481 then
1663
else
1665)
else
(if i.val < 6483 then
1666
else
1670))
else
(if i.val < 6486 then
(if i.val < 6485 then
1678
else
1783)
else
(if i.val < 6487 then
1784
else
1786)))
else
(if i.val < 6492 then
(if i.val < 6490 then
(if i.val < 6489 then
1793
else
1794)
else
(if i.val < 6491 then
1800
else
1804))
else
(if i.val < 6494 then
(if i.val < 6493 then
1805
else
1809)
else
(if i.val < 6495 then
1817
else
1819)))))
else
(if i.val < 6512 then
(if i.val < 6504 then
(if i.val < 6500 then
(if i.val < 6498 then
(if i.val < 6497 then
1827
else
1830)
else
(if i.val < 6499 then
1831
else
1833))
else
(if i.val < 6502 then
(if i.val < 6501 then
1835
else
1839)
else
(if i.val < 6503 then
1840
else
2039)))
else
(if i.val < 6508 then
(if i.val < 6506 then
(if i.val < 6505 then
2043
else
2044)
else
(if i.val < 6507 then
2053
else
2059))
else
(if i.val < 6510 then
(if i.val < 6509 then
2062
else
2063)
else
(if i.val < 6511 then
2064
else
2065))))
else
(if i.val < 6520 then
(if i.val < 6516 then
(if i.val < 6514 then
(if i.val < 6513 then
2070
else
2078)
else
(if i.val < 6515 then
2080
else
2081))
else
(if i.val < 6518 then
(if i.val < 6517 then
2083
else
2090)
else
(if i.val < 6519 then
2091
else
2092)))
else
(if i.val < 6524 then
(if i.val < 6522 then
(if i.val < 6521 then
2095
else
2103)
else
(if i.val < 6523 then
2105
else
2112))
else
(if i.val < 6526 then
(if i.val < 6525 then
2113
else
2117)
else
(if i.val < 6527 then
2118
else
2128)))))))
else
(if i.val < 6592 then
(if i.val < 6560 then
(if i.val < 6544 then
(if i.val < 6536 then
(if i.val < 6532 then
(if i.val < 6530 then
(if i.val < 6529 then
2135
else
2140)
else
(if i.val < 6531 then
2141
else
2142))
else
(if i.val < 6534 then
(if i.val < 6533 then
2155
else
2156)
else
(if i.val < 6535 then
2157
else
2160)))
else
(if i.val < 6540 then
(if i.val < 6538 then
(if i.val < 6537 then
2166
else
2171)
else
(if i.val < 6539 then
2175
else
5403))
else
(if i.val < 6542 then
(if i.val < 6541 then
5769
else
7480)
else
(if i.val < 6543 then
8014
else
7024))))
else
(if i.val < 6552 then
(if i.val < 6548 then
(if i.val < 6546 then
(if i.val < 6545 then
6302
else
5995)
else
(if i.val < 6547 then
5992
else
3683))
else
(if i.val < 6550 then
(if i.val < 6549 then
6722
else
6878)
else
(if i.val < 6551 then
7939
else
4186)))
else
(if i.val < 6556 then
(if i.val < 6554 then
(if i.val < 6553 then
7530
else
4722)
else
(if i.val < 6555 then
4987
else
8242))
else
(if i.val < 6558 then
(if i.val < 6557 then
7255
else
8243)
else
(if i.val < 6559 then
7223
else
7307)))))
else
(if i.val < 6576 then
(if i.val < 6568 then
(if i.val < 6564 then
(if i.val < 6562 then
(if i.val < 6561 then
2593
else
6695)
else
(if i.val < 6563 then
2529
else
2495))
else
(if i.val < 6566 then
(if i.val < 6565 then
6769
else
6730)
else
(if i.val < 6567 then
8244
else
8245)))
else
(if i.val < 6572 then
(if i.val < 6570 then
(if i.val < 6569 then
6253
else
8246)
else
(if i.val < 6571 then
7920
else
7472))
else
(if i.val < 6574 then
(if i.val < 6573 then
7471
else
4414)
else
(if i.val < 6575 then
3270
else
6948))))
else
(if i.val < 6584 then
(if i.val < 6580 then
(if i.val < 6578 then
(if i.val < 6577 then
5724
else
5578)
else
(if i.val < 6579 then
7947
else
5458))
else
(if i.val < 6582 then
(if i.val < 6581 then
6883
else
2433)
else
(if i.val < 6583 then
5934
else
4844)))
else
(if i.val < 6588 then
(if i.val < 6586 then
(if i.val < 6585 then
6037
else
6725)
else
(if i.val < 6587 then
7932
else
3012))
else
(if i.val < 6590 then
(if i.val < 6589 then
8130
else
6164)
else
(if i.val < 6591 then
3359
else
4904))))))
else
(if i.val < 6624 then
(if i.val < 6608 then
(if i.val < 6600 then
(if i.val < 6596 then
(if i.val < 6594 then
(if i.val < 6593 then
6204
else
4719)
else
(if i.val < 6595 then
8247
else
8248))
else
(if i.val < 6598 then
(if i.val < 6597 then
7968
else
2456)
else
(if i.val < 6599 then
7718
else
8249)))
else
(if i.val < 6604 then
(if i.val < 6602 then
(if i.val < 6601 then
5672
else
7233)
else
(if i.val < 6603 then
3585
else
3114))
else
(if i.val < 6606 then
(if i.val < 6605 then
2469
else
8250)
else
(if i.val < 6607 then
4315
else
5110))))
else
(if i.val < 6616 then
(if i.val < 6612 then
(if i.val < 6610 then
(if i.val < 6609 then
5102
else
8251)
else
(if i.val < 6611 then
3477
else
8252))
else
(if i.val < 6614 then
(if i.val < 6613 then
4401
else
8253)
else
(if i.val < 6615 then
7713
else
5161)))
else
(if i.val < 6620 then
(if i.val < 6618 then
(if i.val < 6617 then
4763
else
4634)
else
(if i.val < 6619 then
2635
else
5455))
else
(if i.val < 6622 then
(if i.val < 6621 then
8254
else
4830)
else
(if i.val < 6623 then
5108
else
7224)))))
else
(if i.val < 6640 then
(if i.val < 6632 then
(if i.val < 6628 then
(if i.val < 6626 then
(if i.val < 6625 then
8255
else
3187)
else
(if i.val < 6627 then
6911
else
6038))
else
(if i.val < 6630 then
(if i.val < 6629 then
4851
else
5014)
else
(if i.val < 6631 then
3183
else
6673)))
else
(if i.val < 6636 then
(if i.val < 6634 then
(if i.val < 6633 then
5002
else
4096)
else
(if i.val < 6635 then
6791
else
8256))
else
(if i.val < 6638 then
(if i.val < 6637 then
7232
else
6147)
else
(if i.val < 6639 then
6774
else
7901))))
else
(if i.val < 6648 then
(if i.val < 6644 then
(if i.val < 6642 then
(if i.val < 6641 then
8257
else
6671)
else
(if i.val < 6643 then
6304
else
6150))
else
(if i.val < 6646 then
(if i.val < 6645 then
5152
else
2409)
else
(if i.val < 6647 then
4353
else
5918)))
else
(if i.val < 6652 then
(if i.val < 6650 then
(if i.val < 6649 then
5911
else
6915)
else
(if i.val < 6651 then
5441
else
4632))
else
(if i.val < 6654 then
(if i.val < 6653 then
6682
else
6841)
else
(if i.val < 6655 then
6872
else
4079)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0013 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 6912 then
(if i.val < 6784 then
(if i.val < 6720 then
(if i.val < 6688 then
(if i.val < 6672 then
(if i.val < 6664 then
(if i.val < 6660 then
(if i.val < 6658 then
(if i.val < 6657 then
6916
else
5444)
else
(if i.val < 6659 then
8258
else
5535))
else
(if i.val < 6662 then
(if i.val < 6661 then
3129
else
6183)
else
(if i.val < 6663 then
4847
else
7005)))
else
(if i.val < 6668 then
(if i.val < 6666 then
(if i.val < 6665 then
6047
else
4349)
else
(if i.val < 6667 then
7907
else
7210))
else
(if i.val < 6670 then
(if i.val < 6669 then
5752
else
4727)
else
(if i.val < 6671 then
6674
else
4279))))
else
(if i.val < 6680 then
(if i.val < 6676 then
(if i.val < 6674 then
(if i.val < 6673 then
2733
else
4264)
else
(if i.val < 6675 then
8259
else
7279))
else
(if i.val < 6678 then
(if i.val < 6677 then
6311
else
7510)
else
(if i.val < 6679 then
5835
else
6185)))
else
(if i.val < 6684 then
(if i.val < 6682 then
(if i.val < 6681 then
8260
else
4358)
else
(if i.val < 6683 then
8261
else
8113))
else
(if i.val < 6686 then
(if i.val < 6685 then
4962
else
2223)
else
(if i.val < 6687 then
3299
else
3197)))))
else
(if i.val < 6704 then
(if i.val < 6696 then
(if i.val < 6692 then
(if i.val < 6690 then
(if i.val < 6689 then
7991
else
4377)
else
(if i.val < 6691 then
7482
else
8262))
else
(if i.val < 6694 then
(if i.val < 6693 then
8263
else
2749)
else
(if i.val < 6695 then
7812
else
4126)))
else
(if i.val < 6700 then
(if i.val < 6698 then
(if i.val < 6697 then
8264
else
2611)
else
(if i.val < 6699 then
7468
else
5524))
else
(if i.val < 6702 then
(if i.val < 6701 then
8265
else
5815)
else
(if i.val < 6703 then
4418
else
5696))))
else
(if i.val < 6712 then
(if i.val < 6708 then
(if i.val < 6706 then
(if i.val < 6705 then
3017
else
8266)
else
(if i.val < 6707 then
7811
else
6954))
else
(if i.val < 6710 then
(if i.val < 6709 then
7893
else
4912)
else
(if i.val < 6711 then
7417
else
5538)))
else
(if i.val < 6716 then
(if i.val < 6714 then
(if i.val < 6713 then
8042
else
5831)
else
(if i.val < 6715 then
8267
else
7277))
else
(if i.val < 6718 then
(if i.val < 6717 then
7539
else
7965)
else
(if i.val < 6719 then
8268
else
7385))))))
else
(if i.val < 6752 then
(if i.val < 6736 then
(if i.val < 6728 then
(if i.val < 6724 then
(if i.val < 6722 then
(if i.val < 6721 then
7521
else
7498)
else
(if i.val < 6723 then
4106
else
2775))
else
(if i.val < 6726 then
(if i.val < 6725 then
3631
else
4171)
else
(if i.val < 6727 then
7914
else
8269)))
else
(if i.val < 6732 then
(if i.val < 6730 then
(if i.val < 6729 then
3226
else
7879)
else
(if i.val < 6731 then
4134
else
7809))
else
(if i.val < 6734 then
(if i.val < 6733 then
5853
else
8270)
else
(if i.val < 6735 then
3074
else
3637))))
else
(if i.val < 6744 then
(if i.val < 6740 then
(if i.val < 6738 then
(if i.val < 6737 then
8091
else
3030)
else
(if i.val < 6739 then
7872
else
8271))
else
(if i.val < 6742 then
(if i.val < 6741 then
8272
else
7031)
else
(if i.val < 6743 then
8273
else
7185)))
else
(if i.val < 6748 then
(if i.val < 6746 then
(if i.val < 6745 then
8274
else
6790)
else
(if i.val < 6747 then
2569
else
3121))
else
(if i.val < 6750 then
(if i.val < 6749 then
2241
else
5896)
else
(if i.val < 6751 then
7281
else
6310)))))
else
(if i.val < 6768 then
(if i.val < 6760 then
(if i.val < 6756 then
(if i.val < 6754 then
(if i.val < 6753 then
2654
else
5597)
else
(if i.val < 6755 then
7722
else
5924))
else
(if i.val < 6758 then
(if i.val < 6757 then
7815
else
5565)
else
(if i.val < 6759 then
3651
else
8275)))
else
(if i.val < 6764 then
(if i.val < 6762 then
(if i.val < 6761 then
7993
else
6041)
else
(if i.val < 6763 then
7899
else
7817))
else
(if i.val < 6766 then
(if i.val < 6765 then
7913
else
3214)
else
(if i.val < 6767 then
4980
else
2752))))
else
(if i.val < 6776 then
(if i.val < 6772 then
(if i.val < 6770 then
(if i.val < 6769 then
2984
else
4132)
else
(if i.val < 6771 then
7931
else
8276))
else
(if i.val < 6774 then
(if i.val < 6773 then
8277
else
2490)
else
(if i.val < 6775 then
4276
else
8167)))
else
(if i.val < 6780 then
(if i.val < 6778 then
(if i.val < 6777 then
8278
else
7219)
else
(if i.val < 6779 then
3506
else
7167))
else
(if i.val < 6782 then
(if i.val < 6781 then
7900
else
5760)
else
(if i.val < 6783 then
8279
else
5639)))))))
else
(if i.val < 6848 then
(if i.val < 6816 then
(if i.val < 6800 then
(if i.val < 6792 then
(if i.val < 6788 then
(if i.val < 6786 then
(if i.val < 6785 then
7802
else
5526)
else
(if i.val < 6787 then
5442
else
4988))
else
(if i.val < 6790 then
(if i.val < 6789 then
6684
else
8280)
else
(if i.val < 6791 then
6017
else
4271)))
else
(if i.val < 6796 then
(if i.val < 6794 then
(if i.val < 6793 then
4761
else
5089)
else
(if i.val < 6795 then
8281
else
6173))
else
(if i.val < 6798 then
(if i.val < 6797 then
5426
else
5063)
else
(if i.val < 6799 then
7830
else
5737))))
else
(if i.val < 6808 then
(if i.val < 6804 then
(if i.val < 6802 then
(if i.val < 6801 then
7418
else
6821)
else
(if i.val < 6803 then
6241
else
8282))
else
(if i.val < 6806 then
(if i.val < 6805 then
3738
else
3505)
else
(if i.val < 6807 then
8141
else
7796)))
else
(if i.val < 6812 then
(if i.val < 6810 then
(if i.val < 6809 then
8126
else
3656)
else
(if i.val < 6811 then
3485
else
5745))
else
(if i.val < 6814 then
(if i.val < 6813 then
2260
else
7715)
else
(if i.val < 6815 then
4794
else
5505)))))
else
(if i.val < 6832 then
(if i.val < 6824 then
(if i.val < 6820 then
(if i.val < 6818 then
(if i.val < 6817 then
8028
else
7347)
else
(if i.val < 6819 then
7409
else
8283))
else
(if i.val < 6822 then
(if i.val < 6821 then
8284
else
5662)
else
(if i.val < 6823 then
3617
else
5095)))
else
(if i.val < 6828 then
(if i.val < 6826 then
(if i.val < 6825 then
5413
else
8285)
else
(if i.val < 6827 then
8286
else
6830))
else
(if i.val < 6830 then
(if i.val < 6829 then
6868
else
2252)
else
(if i.val < 6831 then
5717
else
8349))))
else
(if i.val < 6840 then
(if i.val < 6836 then
(if i.val < 6834 then
(if i.val < 6833 then
8386
else
7525)
else
(if i.val < 6835 then
5498
else
8326))
else
(if i.val < 6838 then
(if i.val < 6837 then
3650
else
7029)
else
(if i.val < 6839 then
4996
else
7485)))
else
(if i.val < 6844 then
(if i.val < 6842 then
(if i.val < 6841 then
6955
else
4319)
else
(if i.val < 6843 then
4341
else
7166))
else
(if i.val < 6846 then
(if i.val < 6845 then
8374
else
3088)
else
(if i.val < 6847 then
8368
else
5919))))))
else
(if i.val < 6880 then
(if i.val < 6864 then
(if i.val < 6856 then
(if i.val < 6852 then
(if i.val < 6850 then
(if i.val < 6849 then
4192
else
6772)
else
(if i.val < 6851 then
8354
else
5531))
else
(if i.val < 6854 then
(if i.val < 6853 then
3091
else
3057)
else
(if i.val < 6855 then
7859
else
7191)))
else
(if i.val < 6860 then
(if i.val < 6858 then
(if i.val < 6857 then
5595
else
2201)
else
(if i.val < 6859 then
3763
else
7387))
else
(if i.val < 6862 then
(if i.val < 6861 then
5090
else
6946)
else
(if i.val < 6863 then
7325
else
2232))))
else
(if i.val < 6872 then
(if i.val < 6868 then
(if i.val < 6866 then
(if i.val < 6865 then
3282
else
6907)
else
(if i.val < 6867 then
7397
else
4710))
else
(if i.val < 6870 then
(if i.val < 6869 then
7945
else
6952)
else
(if i.val < 6871 then
5087
else
4810)))
else
(if i.val < 6876 then
(if i.val < 6874 then
(if i.val < 6873 then
7019
else
7412)
else
(if i.val < 6875 then
7294
else
4404))
else
(if i.val < 6878 then
(if i.val < 6877 then
4920
else
7475)
else
(if i.val < 6879 then
4107
else
7276)))))
else
(if i.val < 6896 then
(if i.val < 6888 then
(if i.val < 6884 then
(if i.val < 6882 then
(if i.val < 6881 then
5994
else
5805)
else
(if i.val < 6883 then
5537
else
4165))
else
(if i.val < 6886 then
(if i.val < 6885 then
3113
else
7154)
else
(if i.val < 6887 then
7767
else
6796)))
else
(if i.val < 6892 then
(if i.val < 6890 then
(if i.val < 6889 then
5018
else
6814)
else
(if i.val < 6891 then
4412
else
8410))
else
(if i.val < 6894 then
(if i.val < 6893 then
8170
else
5180)
else
(if i.val < 6895 then
4193
else
8411))))
else
(if i.val < 6904 then
(if i.val < 6900 then
(if i.val < 6898 then
(if i.val < 6897 then
4492
else
6155)
else
(if i.val < 6899 then
7762
else
7757))
else
(if i.val < 6902 then
(if i.val < 6901 then
8027
else
7023)
else
(if i.val < 6903 then
5139
else
7851)))
else
(if i.val < 6908 then
(if i.val < 6906 then
(if i.val < 6905 then
6743
else
6914)
else
(if i.val < 6907 then
7032
else
8408))
else
(if i.val < 6910 then
(if i.val < 6909 then
8316
else
8387)
else
(if i.val < 6911 then
7868
else
4255))))))))
else
(if i.val < 7040 then
(if i.val < 6976 then
(if i.val < 6944 then
(if i.val < 6928 then
(if i.val < 6920 then
(if i.val < 6916 then
(if i.val < 6914 then
(if i.val < 6913 then
2233
else
7170)
else
(if i.val < 6915 then
8041
else
7716))
else
(if i.val < 6918 then
(if i.val < 6917 then
8412
else
2803)
else
(if i.val < 6919 then
5615
else
8159)))
else
(if i.val < 6924 then
(if i.val < 6922 then
(if i.val < 6921 then
7275
else
4964)
else
(if i.val < 6923 then
4364
else
7355))
else
(if i.val < 6926 then
(if i.val < 6925 then
7253
else
7249)
else
(if i.val < 6927 then
6051
else
7921))))
else
(if i.val < 6936 then
(if i.val < 6932 then
(if i.val < 6930 then
(if i.val < 6929 then
2204
else
7849)
else
(if i.val < 6931 then
5795
else
7179))
else
(if i.val < 6934 then
(if i.val < 6933 then
8376
else
4131)
else
(if i.val < 6935 then
5817
else
7836)))
else
(if i.val < 6940 then
(if i.val < 6938 then
(if i.val < 6937 then
7719
else
6942)
else
(if i.val < 6939 then
8318
else
2228))
else
(if i.val < 6942 then
(if i.val < 6941 then
2251
else
8379)
else
(if i.val < 6943 then
4360
else
3033)))))
else
(if i.val < 6960 then
(if i.val < 6952 then
(if i.val < 6948 then
(if i.val < 6946 then
(if i.val < 6945 then
6716
else
4669)
else
(if i.val < 6947 then
7183
else
6189))
else
(if i.val < 6950 then
(if i.val < 6949 then
4149
else
5560)
else
(if i.val < 6951 then
8388
else
4350)))
else
(if i.val < 6956 then
(if i.val < 6954 then
(if i.val < 6953 then
8026
else
7413)
else
(if i.val < 6955 then
5915
else
8413))
else
(if i.val < 6958 then
(if i.val < 6957 then
5175
else
8352)
else
(if i.val < 6959 then
8414
else
5543))))
else
(if i.val < 6968 then
(if i.val < 6964 then
(if i.val < 6962 then
(if i.val < 6961 then
2318
else
7867)
else
(if i.val < 6963 then
4699
else
2193))
else
(if i.val < 6966 then
(if i.val < 6965 then
2293
else
2298)
else
(if i.val < 6967 then
2302
else
2303)))
else
(if i.val < 6972 then
(if i.val < 6970 then
(if i.val < 6969 then
8389
else
8390)
else
(if i.val < 6971 then
7731
else
7768))
else
(if i.val < 6974 then
(if i.val < 6973 then
8391
else
4087)
else
(if i.val < 6975 then
5746
else
2576))))))
else
(if i.val < 7008 then
(if i.val < 6992 then
(if i.val < 6984 then
(if i.val < 6980 then
(if i.val < 6978 then
(if i.val < 6977 then
3249
else
4362)
else
(if i.val < 6979 then
7252
else
8375))
else
(if i.val < 6982 then
(if i.val < 6981 then
2253
else
2254)
else
(if i.val < 6983 then
2256
else
6920)))
else
(if i.val < 6988 then
(if i.val < 6986 then
(if i.val < 6985 then
6906
else
4704)
else
(if i.val < 6987 then
8377
else
8362))
else
(if i.val < 6990 then
(if i.val < 6989 then
4511
else
5077)
else
(if i.val < 6991 then
4682
else
8378))))
else
(if i.val < 7000 then
(if i.val < 6996 then
(if i.val < 6994 then
(if i.val < 6993 then
7709
else
8150)
else
(if i.val < 6995 then
3110
else
7774))
else
(if i.val < 6998 then
(if i.val < 6997 then
8392
else
5935)
else
(if i.val < 6999 then
5518
else
3304)))
else
(if i.val < 7004 then
(if i.val < 7002 then
(if i.val < 7001 then
5517
else
4419)
else
(if i.val < 7003 then
2454
else
7142))
else
(if i.val < 7006 then
(if i.val < 7005 then
7400
else
8393)
else
(if i.val < 7007 then
8140
else
7180)))))
else
(if i.val < 7024 then
(if i.val < 7016 then
(if i.val < 7012 then
(if i.val < 7010 then
(if i.val < 7009 then
5658
else
5904)
else
(if i.val < 7011 then
8288
else
7513))
else
(if i.val < 7014 then
(if i.val < 7013 then
5876
else
2589)
else
(if i.val < 7015 then
7305
else
2525)))
else
(if i.val < 7020 then
(if i.val < 7018 then
(if i.val < 7017 then
8415
else
8416)
else
(if i.val < 7019 then
8171
else
6654))
else
(if i.val < 7022 then
(if i.val < 7021 then
4787
else
3312)
else
(if i.val < 7023 then
5756
else
4325))))
else
(if i.val < 7032 then
(if i.val < 7028 then
(if i.val < 7026 then
(if i.val < 7025 then
4082
else
7526)
else
(if i.val < 7027 then
3250
else
7012))
else
(if i.val < 7030 then
(if i.val < 7029 then
8417
else
4684)
else
(if i.val < 7031 then
8034
else
5801)))
else
(if i.val < 7036 then
(if i.val < 7034 then
(if i.val < 7033 then
6984
else
3379)
else
(if i.val < 7035 then
8418
else
8110))
else
(if i.val < 7038 then
(if i.val < 7037 then
6842
else
8419)
else
(if i.val < 7039 then
7269
else
4092)))))))
else
(if i.val < 7104 then
(if i.val < 7072 then
(if i.val < 7056 then
(if i.val < 7048 then
(if i.val < 7044 then
(if i.val < 7042 then
(if i.val < 7041 then
6665
else
6951)
else
(if i.val < 7043 then
4658
else
6646))
else
(if i.val < 7046 then
(if i.val < 7045 then
7151
else
7287)
else
(if i.val < 7047 then
6681
else
8295)))
else
(if i.val < 7052 then
(if i.val < 7050 then
(if i.val < 7049 then
6977
else
6922)
else
(if i.val < 7051 then
3701
else
8397))
else
(if i.val < 7054 then
(if i.val < 7053 then
6689
else
3392)
else
(if i.val < 7055 then
5407
else
8420))))
else
(if i.val < 7064 then
(if i.val < 7060 then
(if i.val < 7058 then
(if i.val < 7057 then
4444
else
8398)
else
(if i.val < 7059 then
7808
else
6890))
else
(if i.val < 7062 then
(if i.val < 7061 then
6702
else
7001)
else
(if i.val < 7063 then
7228
else
5508)))
else
(if i.val < 7068 then
(if i.val < 7066 then
(if i.val < 7065 then
5587
else
6133)
else
(if i.val < 7067 then
6896
else
8421))
else
(if i.val < 7070 then
(if i.val < 7069 then
7190
else
5539)
else
(if i.val < 7071 then
8422
else
8035)))))
else
(if i.val < 7088 then
(if i.val < 7080 then
(if i.val < 7076 then
(if i.val < 7074 then
(if i.val < 7073 then
7975
else
3233)
else
(if i.val < 7075 then
6988
else
2187))
else
(if i.val < 7078 then
(if i.val < 7077 then
2188
else
2198)
else
(if i.val < 7079 then
2219
else
2221)))
else
(if i.val < 7084 then
(if i.val < 7082 then
(if i.val < 7081 then
2222
else
2238)
else
(if i.val < 7083 then
2239
else
2263))
else
(if i.val < 7086 then
(if i.val < 7085 then
2312
else
2314)
else
(if i.val < 7087 then
2316
else
2319))))
else
(if i.val < 7096 then
(if i.val < 7092 then
(if i.val < 7090 then
(if i.val < 7089 then
2324
else
2328)
else
(if i.val < 7091 then
2417
else
2419))
else
(if i.val < 7094 then
(if i.val < 7093 then
2423
else
2428)
else
(if i.val < 7095 then
2429
else
2438)))
else
(if i.val < 7100 then
(if i.val < 7098 then
(if i.val < 7097 then
2450
else
2453)
else
(if i.val < 7099 then
2462
else
2463))
else
(if i.val < 7102 then
(if i.val < 7101 then
2464
else
2465)
else
(if i.val < 7103 then
6651
else
6166))))))
else
(if i.val < 7136 then
(if i.val < 7120 then
(if i.val < 7112 then
(if i.val < 7108 then
(if i.val < 7106 then
(if i.val < 7105 then
5468
else
7495)
else
(if i.val < 7107 then
8423
else
8424))
else
(if i.val < 7110 then
(if i.val < 7109 then
7262
else
2637)
else
(if i.val < 7111 then
4986
else
5689)))
else
(if i.val < 7116 then
(if i.val < 7114 then
(if i.val < 7113 then
5626
else
7465)
else
(if i.val < 7115 then
8425
else
6945))
else
(if i.val < 7118 then
(if i.val < 7117 then
8426
else
5894)
else
(if i.val < 7119 then
6990
else
8400))))
else
(if i.val < 7128 then
(if i.val < 7124 then
(if i.val < 7122 then
(if i.val < 7121 then
7750
else
5659)
else
(if i.val < 7123 then
8039
else
3153))
else
(if i.val < 7126 then
(if i.val < 7125 then
4921
else
6985)
else
(if i.val < 7127 then
4688
else
6867)))
else
(if i.val < 7132 then
(if i.val < 7130 then
(if i.val < 7129 then
4692
else
8427)
else
(if i.val < 7131 then
6795
else
7978))
else
(if i.val < 7134 then
(if i.val < 7133 then
5126
else
7814)
else
(if i.val < 7135 then
2597
else
2650)))))
else
(if i.val < 7152 then
(if i.val < 7144 then
(if i.val < 7140 then
(if i.val < 7138 then
(if i.val < 7137 then
2755
else
6811)
else
(if i.val < 7139 then
2564
else
3309))
else
(if i.val < 7142 then
(if i.val < 7141 then
2547
else
3275)
else
(if i.val < 7143 then
7193
else
8395)))
else
(if i.val < 7148 then
(if i.val < 7146 then
(if i.val < 7145 then
5722
else
7923)
else
(if i.val < 7147 then
6296
else
4819))
else
(if i.val < 7150 then
(if i.val < 7149 then
6176
else
6675)
else
(if i.val < 7151 then
4333
else
4354))))
else
(if i.val < 7160 then
(if i.val < 7156 then
(if i.val < 7154 then
(if i.val < 7153 then
8428
else
8429)
else
(if i.val < 7155 then
8430
else
8431))
else
(if i.val < 7158 then
(if i.val < 7157 then
8432
else
6892)
else
(if i.val < 7159 then
8364
else
5007)))
else
(if i.val < 7164 then
(if i.val < 7162 then
(if i.val < 7161 then
6193
else
4464)
else
(if i.val < 7163 then
7748
else
3108))
else
(if i.val < 7166 then
(if i.val < 7165 then
5552
else
7793)
else
(if i.val < 7167 then
6148
else
4693)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0014 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 7424 then
(if i.val < 7296 then
(if i.val < 7232 then
(if i.val < 7200 then
(if i.val < 7184 then
(if i.val < 7176 then
(if i.val < 7172 then
(if i.val < 7170 then
(if i.val < 7169 then
2578
else
7878)
else
(if i.val < 7171 then
7969
else
3715))
else
(if i.val < 7174 then
(if i.val < 7173 then
5926
else
8115)
else
(if i.val < 7175 then
7841
else
8433)))
else
(if i.val < 7180 then
(if i.val < 7178 then
(if i.val < 7177 then
7463
else
8434)
else
(if i.val < 7179 then
4985
else
4452))
else
(if i.val < 7182 then
(if i.val < 7181 then
7188
else
5590)
else
(if i.val < 7183 then
8372
else
6861))))
else
(if i.val < 7192 then
(if i.val < 7188 then
(if i.val < 7186 then
(if i.val < 7185 then
8435
else
6904)
else
(if i.val < 7187 then
8343
else
8302))
else
(if i.val < 7190 then
(if i.val < 7189 then
7007
else
8436)
else
(if i.val < 7191 then
4499
else
8136)))
else
(if i.val < 7196 then
(if i.val < 7194 then
(if i.val < 7193 then
5747
else
7003)
else
(if i.val < 7195 then
8292
else
8311))
else
(if i.val < 7198 then
(if i.val < 7197 then
5641
else
7008)
else
(if i.val < 7199 then
2579
else
6231)))))
else
(if i.val < 7216 then
(if i.val < 7208 then
(if i.val < 7204 then
(if i.val < 7202 then
(if i.val < 7201 then
5647
else
7148)
else
(if i.val < 7203 then
6755
else
5469))
else
(if i.val < 7206 then
(if i.val < 7205 then
6056
else
6764)
else
(if i.val < 7207 then
7523
else
7017)))
else
(if i.val < 7212 then
(if i.val < 7210 then
(if i.val < 7209 then
7816
else
5640)
else
(if i.val < 7211 then
7494
else
4163))
else
(if i.val < 7214 then
(if i.val < 7213 then
7408
else
8104)
else
(if i.val < 7215 then
4789
else
8509))))
else
(if i.val < 7224 then
(if i.val < 7220 then
(if i.val < 7218 then
(if i.val < 7217 then
7488
else
2584)
else
(if i.val < 7219 then
8489
else
7308))
else
(if i.val < 7222 then
(if i.val < 7221 then
7751
else
4344)
else
(if i.val < 7223 then
4121
else
4120)))
else
(if i.val < 7228 then
(if i.val < 7226 then
(if i.val < 7225 then
4251
else
8321)
else
(if i.val < 7227 then
3159
else
8459))
else
(if i.val < 7230 then
(if i.val < 7229 then
4420
else
8482)
else
(if i.val < 7231 then
6175
else
6792))))))
else
(if i.val < 7264 then
(if i.val < 7248 then
(if i.val < 7240 then
(if i.val < 7236 then
(if i.val < 7234 then
(if i.val < 7233 then
4274
else
4202)
else
(if i.val < 7235 then
3163
else
6807))
else
(if i.val < 7238 then
(if i.val < 7237 then
8138
else
2509)
else
(if i.val < 7239 then
5859
else
7227)))
else
(if i.val < 7244 then
(if i.val < 7242 then
(if i.val < 7241 then
5670
else
5668)
else
(if i.val < 7243 then
6900
else
7020))
else
(if i.val < 7246 then
(if i.val < 7245 then
7491
else
7214)
else
(if i.val < 7247 then
5594
else
2478))))
else
(if i.val < 7256 then
(if i.val < 7252 then
(if i.val < 7250 then
(if i.val < 7249 then
6295
else
4292)
else
(if i.val < 7251 then
8336
else
2725))
else
(if i.val < 7254 then
(if i.val < 7253 then
7786
else
7807)
else
(if i.val < 7255 then
2588
else
4118)))
else
(if i.val < 7260 then
(if i.val < 7258 then
(if i.val < 7257 then
4871
else
5719)
else
(if i.val < 7259 then
7972
else
4829))
else
(if i.val < 7262 then
(if i.val < 7261 then
5629
else
7344)
else
(if i.val < 7263 then
4652
else
5734)))))
else
(if i.val < 7280 then
(if i.val < 7272 then
(if i.val < 7268 then
(if i.val < 7266 then
(if i.val < 7265 then
4162
else
5725)
else
(if i.val < 7267 then
8476
else
8457))
else
(if i.val < 7270 then
(if i.val < 7269 then
7290
else
4347)
else
(if i.val < 7271 then
7261
else
7266)))
else
(if i.val < 7276 then
(if i.val < 7274 then
(if i.val < 7273 then
7348
else
7903)
else
(if i.val < 7275 then
7789
else
6983))
else
(if i.val < 7278 then
(if i.val < 7277 then
5991
else
7890)
else
(if i.val < 7279 then
5405
else
7149))))
else
(if i.val < 7288 then
(if i.val < 7284 then
(if i.val < 7282 then
(if i.val < 7281 then
5821
else
6011)
else
(if i.val < 7283 then
8497
else
7721))
else
(if i.val < 7286 then
(if i.val < 7285 then
6793
else
3357)
else
(if i.val < 7287 then
4098
else
4355)))
else
(if i.val < 7292 then
(if i.val < 7290 then
(if i.val < 7289 then
5131
else
3119)
else
(if i.val < 7291 then
8484
else
8347))
else
(if i.val < 7294 then
(if i.val < 7293 then
5802
else
6844)
else
(if i.val < 7295 then
8538
else
7218)))))))
else
(if i.val < 7360 then
(if i.val < 7328 then
(if i.val < 7312 then
(if i.val < 7304 then
(if i.val < 7300 then
(if i.val < 7298 then
(if i.val < 7297 then
7877
else
4673)
else
(if i.val < 7299 then
7416
else
8160))
else
(if i.val < 7302 then
(if i.val < 7301 then
7337
else
8176)
else
(if i.val < 7303 then
7522
else
4694)))
else
(if i.val < 7308 then
(if i.val < 7306 then
(if i.val < 7305 then
6238
else
7542)
else
(if i.val < 7307 then
2594
else
4124))
else
(if i.val < 7310 then
(if i.val < 7309 then
6777
else
7410)
else
(if i.val < 7311 then
6986
else
7162))))
else
(if i.val < 7320 then
(if i.val < 7316 then
(if i.val < 7314 then
(if i.val < 7313 then
5854
else
5663)
else
(if i.val < 7315 then
5664
else
8539))
else
(if i.val < 7318 then
(if i.val < 7317 then
6949
else
7746)
else
(if i.val < 7319 then
7184
else
7749)))
else
(if i.val < 7324 then
(if i.val < 7322 then
(if i.val < 7321 then
8346
else
7769)
else
(if i.val < 7323 then
7351
else
7022))
else
(if i.val < 7326 then
(if i.val < 7325 then
5176
else
6303)
else
(if i.val < 7327 then
4907
else
6979)))))
else
(if i.val < 7344 then
(if i.val < 7336 then
(if i.val < 7332 then
(if i.val < 7330 then
(if i.val < 7329 then
8106
else
4960)
else
(if i.val < 7331 then
5548
else
3632))
else
(if i.val < 7334 then
(if i.val < 7333 then
7383
else
5187)
else
(if i.val < 7335 then
6677
else
4952)))
else
(if i.val < 7340 then
(if i.val < 7338 then
(if i.val < 7337 then
7511
else
6312)
else
(if i.val < 7339 then
6992
else
8445))
else
(if i.val < 7342 then
(if i.val < 7341 then
7484
else
7739)
else
(if i.val < 7343 then
6823
else
5610))))
else
(if i.val < 7352 then
(if i.val < 7348 then
(if i.val < 7346 then
(if i.val < 7345 then
7270
else
8521)
else
(if i.val < 7347 then
8540
else
5478))
else
(if i.val < 7350 then
(if i.val < 7349 then
7775
else
8503)
else
(if i.val < 7351 then
6000
else
8541)))
else
(if i.val < 7356 then
(if i.val < 7354 then
(if i.val < 7353 then
5942
else
3732)
else
(if i.val < 7355 then
5943
else
4381))
else
(if i.val < 7358 then
(if i.val < 7357 then
8148
else
3295)
else
(if i.val < 7359 then
5591
else
5822))))))
else
(if i.val < 7392 then
(if i.val < 7376 then
(if i.val < 7368 then
(if i.val < 7364 then
(if i.val < 7362 then
(if i.val < 7361 then
6871
else
5159)
else
(if i.val < 7363 then
2614
else
2712))
else
(if i.val < 7366 then
(if i.val < 7365 then
2713
else
5885)
else
(if i.val < 7367 then
2721
else
5852)))
else
(if i.val < 7372 then
(if i.val < 7370 then
(if i.val < 7369 then
7797
else
6870)
else
(if i.val < 7371 then
4875
else
8290))
else
(if i.val < 7374 then
(if i.val < 7373 then
5945
else
2596)
else
(if i.val < 7375 then
2634
else
7335))))
else
(if i.val < 7384 then
(if i.val < 7380 then
(if i.val < 7378 then
(if i.val < 7377 then
6013
else
3042)
else
(if i.val < 7379 then
3255
else
5427))
else
(if i.val < 7382 then
(if i.val < 7381 then
5417
else
8350)
else
(if i.val < 7383 then
8501
else
8542)))
else
(if i.val < 7388 then
(if i.val < 7386 then
(if i.val < 7385 then
7537
else
4822)
else
(if i.val < 7387 then
8287
else
8502))
else
(if i.val < 7390 then
(if i.val < 7389 then
7538
else
3281)
else
(if i.val < 7391 then
4973
else
7756)))))
else
(if i.val < 7408 then
(if i.val < 7400 then
(if i.val < 7396 then
(if i.val < 7394 then
(if i.val < 7393 then
8151
else
5798)
else
(if i.val < 7395 then
7856
else
7755))
else
(if i.val < 7398 then
(if i.val < 7397 then
5933
else
7917)
else
(if i.val < 7399 then
8543
else
7333)))
else
(if i.val < 7404 then
(if i.val < 7402 then
(if i.val < 7401 then
6244
else
6688)
else
(if i.val < 7403 then
7492
else
5481))
else
(if i.val < 7406 then
(if i.val < 7405 then
5542
else
7837)
else
(if i.val < 7407 then
6824
else
7958))))
else
(if i.val < 7416 then
(if i.val < 7412 then
(if i.val < 7410 then
(if i.val < 7409 then
5996
else
8097)
else
(if i.val < 7411 then
7457
else
6813))
else
(if i.val < 7414 then
(if i.val < 7413 then
8544
else
8168)
else
(if i.val < 7415 then
6690
else
5632)))
else
(if i.val < 7420 then
(if i.val < 7418 then
(if i.val < 7417 then
6306
else
4468)
else
(if i.val < 7419 then
8049
else
3634))
else
(if i.val < 7422 then
(if i.val < 7421 then
8510
else
8453)
else
(if i.val < 7423 then
3257
else
2501))))))))
else
(if i.val < 7552 then
(if i.val < 7488 then
(if i.val < 7456 then
(if i.val < 7440 then
(if i.val < 7432 then
(if i.val < 7428 then
(if i.val < 7426 then
(if i.val < 7425 then
2532
else
2533)
else
(if i.val < 7427 then
2535
else
2536))
else
(if i.val < 7430 then
(if i.val < 7429 then
2537
else
2548)
else
(if i.val < 7431 then
2726
else
2732)))
else
(if i.val < 7436 then
(if i.val < 7434 then
(if i.val < 7433 then
2740
else
2741)
else
(if i.val < 7435 then
2742
else
2743))
else
(if i.val < 7438 then
(if i.val < 7437 then
2746
else
2751)
else
(if i.val < 7439 then
2753
else
6860))))
else
(if i.val < 7448 then
(if i.val < 7444 then
(if i.val < 7442 then
(if i.val < 7441 then
7743
else
8300)
else
(if i.val < 7443 then
8511
else
4153))
else
(if i.val < 7446 then
(if i.val < 7445 then
5421
else
7790)
else
(if i.val < 7447 then
8512
else
6171)))
else
(if i.val < 7452 then
(if i.val < 7450 then
(if i.val < 7449 then
7994
else
3085)
else
(if i.val < 7451 then
5559
else
2662))
else
(if i.val < 7454 then
(if i.val < 7453 then
2482
else
7132)
else
(if i.val < 7455 then
8496
else
7874)))))
else
(if i.val < 7472 then
(if i.val < 7464 then
(if i.val < 7460 then
(if i.val < 7458 then
(if i.val < 7457 then
5179
else
7309)
else
(if i.val < 7459 then
2599
else
2600))
else
(if i.val < 7462 then
(if i.val < 7461 then
2642
else
2645)
else
(if i.val < 7463 then
2646
else
7792)))
else
(if i.val < 7468 then
(if i.val < 7466 then
(if i.val < 7465 then
3318
else
4663)
else
(if i.val < 7467 then
8483
else
2982))
else
(if i.val < 7470 then
(if i.val < 7469 then
4666
else
4147)
else
(if i.val < 7471 then
3069
else
4145))))
else
(if i.val < 7480 then
(if i.val < 7476 then
(if i.val < 7474 then
(if i.val < 7473 then
4143
else
5490)
else
(if i.val < 7475 then
5519
else
8498))
else
(if i.val < 7478 then
(if i.val < 7477 then
8289
else
8505)
else
(if i.val < 7479 then
5606
else
4998)))
else
(if i.val < 7484 then
(if i.val < 7482 then
(if i.val < 7481 then
4072
else
8513)
else
(if i.val < 7483 then
7414
else
2657))
else
(if i.val < 7486 then
(if i.val < 7485 then
4905
else
4318)
else
(if i.val < 7487 then
8329
else
8128))))))
else
(if i.val < 7520 then
(if i.val < 7504 then
(if i.val < 7496 then
(if i.val < 7492 then
(if i.val < 7490 then
(if i.val < 7489 then
8514
else
5006)
else
(if i.val < 7491 then
8508
else
4788))
else
(if i.val < 7494 then
(if i.val < 7493 then
5781
else
6785)
else
(if i.val < 7495 then
6667
else
4645)))
else
(if i.val < 7500 then
(if i.val < 7498 then
(if i.val < 7497 then
8515
else
7398)
else
(if i.val < 7499 then
7777
else
7330))
else
(if i.val < 7502 then
(if i.val < 7501 then
3043
else
6212)
else
(if i.val < 7503 then
6880
else
3371))))
else
(if i.val < 7512 then
(if i.val < 7508 then
(if i.val < 7506 then
(if i.val < 7505 then
6921
else
8534)
else
(if i.val < 7507 then
2761
else
7858))
else
(if i.val < 7510 then
(if i.val < 7509 then
8144
else
3320)
else
(if i.val < 7511 then
7334
else
7710)))
else
(if i.val < 7516 then
(if i.val < 7514 then
(if i.val < 7513 then
8133
else
8143)
else
(if i.val < 7515 then
7248
else
5459))
else
(if i.val < 7518 then
(if i.val < 7517 then
5614
else
2805)
else
(if i.val < 7519 then
2565
else
4852)))))
else
(if i.val < 7536 then
(if i.val < 7528 then
(if i.val < 7524 then
(if i.val < 7522 then
(if i.val < 7521 then
4795
else
5577)
else
(if i.val < 7523 then
4797
else
8504))
else
(if i.val < 7526 then
(if i.val < 7525 then
3118
else
4832)
else
(if i.val < 7527 then
7871
else
4647)))
else
(if i.val < 7532 then
(if i.val < 7530 then
(if i.val < 7529 then
4726
else
7829)
else
(if i.val < 7531 then
4110
else
8545))
else
(if i.val < 7534 then
(if i.val < 7533 then
3212
else
5558)
else
(if i.val < 7535 then
6307
else
6899))))
else
(if i.val < 7544 then
(if i.val < 7540 then
(if i.val < 7538 then
(if i.val < 7537 then
7283
else
5920)
else
(if i.val < 7539 then
8535
else
6944))
else
(if i.val < 7542 then
(if i.val < 7541 then
8438
else
5164)
else
(if i.val < 7543 then
7014
else
4091)))
else
(if i.val < 7548 then
(if i.val < 7546 then
(if i.val < 7545 then
3051
else
6187)
else
(if i.val < 7547 then
5687
else
2985))
else
(if i.val < 7550 then
(if i.val < 7549 then
4653
else
8441)
else
(if i.val < 7551 then
6213
else
7259)))))))
else
(if i.val < 7616 then
(if i.val < 7584 then
(if i.val < 7568 then
(if i.val < 7560 then
(if i.val < 7556 then
(if i.val < 7554 then
(if i.val < 7553 then
3215
else
3751)
else
(if i.val < 7555 then
6662
else
5464))
else
(if i.val < 7558 then
(if i.val < 7557 then
5708
else
7519)
else
(if i.val < 7559 then
7726
else
3338)))
else
(if i.val < 7564 then
(if i.val < 7562 then
(if i.val < 7561 then
8449
else
5674)
else
(if i.val < 7563 then
8546
else
3722))
else
(if i.val < 7566 then
(if i.val < 7565 then
8399
else
7256)
else
(if i.val < 7567 then
8121
else
4747))))
else
(if i.val < 7576 then
(if i.val < 7572 then
(if i.val < 7570 then
(if i.val < 7569 then
5060
else
8518)
else
(if i.val < 7571 then
6018
else
7326))
else
(if i.val < 7574 then
(if i.val < 7573 then
8547
else
6709)
else
(if i.val < 7575 then
4270
else
4701)))
else
(if i.val < 7580 then
(if i.val < 7578 then
(if i.val < 7577 then
6876
else
3684)
else
(if i.val < 7579 then
6301
else
6787))
else
(if i.val < 7582 then
(if i.val < 7581 then
2999
else
4805)
else
(if i.val < 7583 then
6838
else
7479)))))
else
(if i.val < 7600 then
(if i.val < 7592 then
(if i.val < 7588 then
(if i.val < 7586 then
(if i.val < 7585 then
5416
else
4738)
else
(if i.val < 7587 then
3772
else
7489))
else
(if i.val < 7590 then
(if i.val < 7589 then
7159
else
2798)
else
(if i.val < 7591 then
5171
else
5794)))
else
(if i.val < 7596 then
(if i.val < 7594 then
(if i.val < 7593 then
4484
else
5173)
else
(if i.val < 7595 then
3112
else
8342))
else
(if i.val < 7598 then
(if i.val < 7597 then
5582
else
3478)
else
(if i.val < 7599 then
4814
else
7541))))
else
(if i.val < 7608 then
(if i.val < 7604 then
(if i.val < 7602 then
(if i.val < 7601 then
5814
else
4337)
else
(if i.val < 7603 then
8548
else
6956))
else
(if i.val < 7606 then
(if i.val < 7605 then
7324
else
7456)
else
(if i.val < 7607 then
6893
else
4969)))
else
(if i.val < 7612 then
(if i.val < 7610 then
(if i.val < 7609 then
2483
else
2484)
else
(if i.val < 7611 then
2508
else
2510))
else
(if i.val < 7614 then
(if i.val < 7613 then
2511
else
2556)
else
(if i.val < 7615 then
2558
else
2603))))))
else
(if i.val < 7648 then
(if i.val < 7632 then
(if i.val < 7624 then
(if i.val < 7620 then
(if i.val < 7618 then
(if i.val < 7617 then
2605
else
2608)
else
(if i.val < 7619 then
2609
else
2658))
else
(if i.val < 7622 then
(if i.val < 7621 then
2660
else
2664)
else
(if i.val < 7623 then
2776
else
2780)))
else
(if i.val < 7628 then
(if i.val < 7626 then
(if i.val < 7625 then
2781
else
2793)
else
(if i.val < 7627 then
2800
else
2801))
else
(if i.val < 7630 then
(if i.val < 7629 then
2802
else
2804)
else
(if i.val < 7631 then
2808
else
2809))))
else
(if i.val < 7640 then
(if i.val < 7636 then
(if i.val < 7634 then
(if i.val < 7633 then
2992
else
2998)
else
(if i.val < 7635 then
3003
else
3009))
else
(if i.val < 7638 then
(if i.val < 7637 then
3025
else
3026)
else
(if i.val < 7639 then
3027
else
3038)))
else
(if i.val < 7644 then
(if i.val < 7642 then
(if i.val < 7641 then
3047
else
3048)
else
(if i.val < 7643 then
3053
else
3061))
else
(if i.val < 7646 then
(if i.val < 7645 then
3068
else
3082)
else
(if i.val < 7647 then
3083
else
3086)))))
else
(if i.val < 7664 then
(if i.val < 7656 then
(if i.val < 7652 then
(if i.val < 7650 then
(if i.val < 7649 then
3097
else
7278)
else
(if i.val < 7651 then
8145
else
8131))
else
(if i.val < 7654 then
(if i.val < 7653 then
7380
else
7379)
else
(if i.val < 7655 then
3254
else
8487)))
else
(if i.val < 7660 then
(if i.val < 7658 then
(if i.val < 7657 then
5497
else
3109)
else
(if i.val < 7659 then
6650
else
6786))
else
(if i.val < 7662 then
(if i.val < 7661 then
5770
else
6657)
else
(if i.val < 7663 then
8366
else
4368))))
else
(if i.val < 7672 then
(if i.val < 7668 then
(if i.val < 7666 then
(if i.val < 7665 then
7732
else
4324)
else
(if i.val < 7667 then
4303
else
8100))
else
(if i.val < 7670 then
(if i.val < 7669 then
7515
else
5843)
else
(if i.val < 7671 then
4833
else
3464)))
else
(if i.val < 7676 then
(if i.val < 7674 then
(if i.val < 7673 then
3460
else
5700)
else
(if i.val < 7675 then
6292
else
7403))
else
(if i.val < 7678 then
(if i.val < 7677 then
7744
else
7473)
else
(if i.val < 7679 then
4891
else
5901)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0015 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 7936 then
(if i.val < 7808 then
(if i.val < 7744 then
(if i.val < 7712 then
(if i.val < 7696 then
(if i.val < 7688 then
(if i.val < 7684 then
(if i.val < 7682 then
(if i.val < 7681 then
8549
else
5839)
else
(if i.val < 7683 then
8109
else
8337))
else
(if i.val < 7686 then
(if i.val < 7685 then
5059
else
7000)
else
(if i.val < 7687 then
6998
else
5872)))
else
(if i.val < 7692 then
(if i.val < 7690 then
(if i.val < 7689 then
4982
else
8550)
else
(if i.val < 7691 then
7989
else
6851))
else
(if i.val < 7694 then
(if i.val < 7693 then
4400
else
6659)
else
(if i.val < 7695 then
7876
else
6882))))
else
(if i.val < 7704 then
(if i.val < 7700 then
(if i.val < 7698 then
(if i.val < 7697 then
6711
else
8551)
else
(if i.val < 7699 then
4771
else
7404))
else
(if i.val < 7702 then
(if i.val < 7701 then
6959
else
4767)
else
(if i.val < 7703 then
7720
else
5754)))
else
(if i.val < 7708 then
(if i.val < 7706 then
(if i.val < 7705 then
5950
else
8479)
else
(if i.val < 7707 then
8552
else
7533))
else
(if i.val < 7710 then
(if i.val < 7709 then
6757
else
7338)
else
(if i.val < 7711 then
7336
else
3365)))))
else
(if i.val < 7728 then
(if i.val < 7720 then
(if i.val < 7716 then
(if i.val < 7714 then
(if i.val < 7713 then
3384
else
4230)
else
(if i.val < 7715 then
3667
else
7411))
else
(if i.val < 7718 then
(if i.val < 7717 then
6649
else
5779)
else
(if i.val < 7719 then
4194
else
4462)))
else
(if i.val < 7724 then
(if i.val < 7722 then
(if i.val < 7721 then
5549
else
7536)
else
(if i.val < 7723 then
5580
else
7487))
else
(if i.val < 7726 then
(if i.val < 7725 then
6029
else
8124)
else
(if i.val < 7727 then
4854
else
7865))))
else
(if i.val < 7736 then
(if i.val < 7732 then
(if i.val < 7730 then
(if i.val < 7729 then
8402
else
8553)
else
(if i.val < 7731 then
8554
else
4469))
else
(if i.val < 7734 then
(if i.val < 7733 then
5450
else
4382)
else
(if i.val < 7735 then
7922
else
7250)))
else
(if i.val < 7740 then
(if i.val < 7738 then
(if i.val < 7737 then
8305
else
8555)
else
(if i.val < 7739 then
6789
else
7906))
else
(if i.val < 7742 then
(if i.val < 7741 then
8556
else
6726)
else
(if i.val < 7743 then
3169
else
5092))))))
else
(if i.val < 7776 then
(if i.val < 7760 then
(if i.val < 7752 then
(if i.val < 7748 then
(if i.val < 7746 then
(if i.val < 7745 then
5482
else
8557)
else
(if i.val < 7747 then
4804
else
8313))
else
(if i.val < 7750 then
(if i.val < 7749 then
7311
else
8558)
else
(if i.val < 7751 then
4689
else
8517)))
else
(if i.val < 7756 then
(if i.val < 7754 then
(if i.val < 7753 then
6738
else
8559)
else
(if i.val < 7755 then
8560
else
7781))
else
(if i.val < 7758 then
(if i.val < 7757 then
7934
else
7535)
else
(if i.val < 7759 then
3235
else
6282))))
else
(if i.val < 7768 then
(if i.val < 7764 then
(if i.val < 7762 then
(if i.val < 7761 then
7896
else
7199)
else
(if i.val < 7763 then
5106
else
6668))
else
(if i.val < 7766 then
(if i.val < 7765 then
7407
else
6771)
else
(if i.val < 7767 then
6678
else
4793)))
else
(if i.val < 7772 then
(if i.val < 7770 then
(if i.val < 7769 then
4471
else
8485)
else
(if i.val < 7771 then
8561
else
4299))
else
(if i.val < 7774 then
(if i.val < 7773 then
3307
else
8294)
else
(if i.val < 7775 then
8478
else
7272)))))
else
(if i.val < 7792 then
(if i.val < 7784 then
(if i.val < 7780 then
(if i.val < 7778 then
(if i.val < 7777 then
8562
else
6721)
else
(if i.val < 7779 then
8458
else
5588))
else
(if i.val < 7782 then
(if i.val < 7781 then
6799
else
7395)
else
(if i.val < 7783 then
3256
else
6850)))
else
(if i.val < 7788 then
(if i.val < 7786 then
(if i.val < 7785 then
6993
else
8563)
else
(if i.val < 7787 then
6978
else
6220))
else
(if i.val < 7790 then
(if i.val < 7789 then
5160
else
8529)
else
(if i.val < 7791 then
5109
else
6032))))
else
(if i.val < 7800 then
(if i.val < 7796 then
(if i.val < 7794 then
(if i.val < 7793 then
7176
else
5899)
else
(if i.val < 7795 then
8384
else
8564))
else
(if i.val < 7798 then
(if i.val < 7797 then
7235
else
5084)
else
(if i.val < 7799 then
6264
else
8565)))
else
(if i.val < 7804 then
(if i.val < 7802 then
(if i.val < 7801 then
7263
else
8570)
else
(if i.val < 7803 then
7895
else
3223))
else
(if i.val < 7806 then
(if i.val < 7805 then
5669
else
7959)
else
(if i.val < 7807 then
7760
else
6924)))))))
else
(if i.val < 7872 then
(if i.val < 7840 then
(if i.val < 7824 then
(if i.val < 7816 then
(if i.val < 7812 then
(if i.val < 7810 then
(if i.val < 7809 then
4411
else
8046)
else
(if i.val < 7811 then
7496
else
6320))
else
(if i.val < 7814 then
(if i.val < 7813 then
8132
else
8111)
else
(if i.val < 7815 then
8531
else
8584)))
else
(if i.val < 7820 then
(if i.val < 7818 then
(if i.val < 7817 then
8471
else
8155)
else
(if i.val < 7819 then
7737
else
4223))
else
(if i.val < 7822 then
(if i.val < 7821 then
7225
else
3198)
else
(if i.val < 7823 then
6703
else
5650))))
else
(if i.val < 7832 then
(if i.val < 7828 then
(if i.val < 7826 then
(if i.val < 7825 then
8569
else
7887)
else
(if i.val < 7827 then
4180
else
8045))
else
(if i.val < 7830 then
(if i.val < 7829 then
8044
else
5419)
else
(if i.val < 7831 then
7962
else
7759)))
else
(if i.val < 7836 then
(if i.val < 7834 then
(if i.val < 7833 then
6825
else
4758)
else
(if i.val < 7835 then
7339
else
5884))
else
(if i.val < 7838 then
(if i.val < 7837 then
4461
else
5178)
else
(if i.val < 7839 then
7129
else
7963)))))
else
(if i.val < 7856 then
(if i.val < 7848 then
(if i.val < 7844 then
(if i.val < 7842 then
(if i.val < 7841 then
8152
else
4756)
else
(if i.val < 7843 then
8098
else
8589))
else
(if i.val < 7846 then
(if i.val < 7845 then
7016
else
3144)
else
(if i.val < 7847 then
7486
else
5830)))
else
(if i.val < 7852 then
(if i.val < 7850 then
(if i.val < 7849 then
3260
else
4446)
else
(if i.val < 7851 then
3171
else
4445))
else
(if i.val < 7854 then
(if i.val < 7853 then
5829
else
5740)
else
(if i.val < 7855 then
8456
else
8588))))
else
(if i.val < 7864 then
(if i.val < 7860 then
(if i.val < 7858 then
(if i.val < 7857 then
5545
else
7356)
else
(if i.val < 7859 then
7992
else
4313))
else
(if i.val < 7862 then
(if i.val < 7861 then
3186
else
3199)
else
(if i.val < 7863 then
3201
else
5574)))
else
(if i.val < 7868 then
(if i.val < 7866 then
(if i.val < 7865 then
4917
else
5584)
else
(if i.val < 7867 then
6010
else
4293))
else
(if i.val < 7870 then
(if i.val < 7869 then
4327
else
5583)
else
(if i.val < 7871 then
5130
else
7025))))))
else
(if i.val < 7904 then
(if i.val < 7888 then
(if i.val < 7880 then
(if i.val < 7876 then
(if i.val < 7874 then
(if i.val < 7873 then
7752
else
8315)
else
(if i.val < 7875 then
5429
else
3347))
else
(if i.val < 7878 then
(if i.val < 7877 then
5536
else
5579)
else
(if i.val < 7879 then
7919
else
5474)))
else
(if i.val < 7884 then
(if i.val < 7882 then
(if i.val < 7881 then
6168
else
6718)
else
(if i.val < 7883 then
4826
else
4085))
else
(if i.val < 7886 then
(if i.val < 7885 then
5767
else
5758)
else
(if i.val < 7887 then
7892
else
5609))))
else
(if i.val < 7896 then
(if i.val < 7892 then
(if i.val < 7890 then
(if i.val < 7889 then
3236
else
5759)
else
(if i.val < 7891 then
6715
else
7754))
else
(if i.val < 7894 then
(if i.val < 7893 then
8335
else
8442)
else
(if i.val < 7895 then
5990
else
6784)))
else
(if i.val < 7900 then
(if i.val < 7898 then
(if i.val < 7897 then
7806
else
6184)
else
(if i.val < 7899 then
6742
else
8613))
else
(if i.val < 7902 then
(if i.val < 7901 then
5098
else
4277)
else
(if i.val < 7903 then
7320
else
8614)))))
else
(if i.val < 7920 then
(if i.val < 7912 then
(if i.val < 7908 then
(if i.val < 7906 then
(if i.val < 7905 then
7884
else
7501)
else
(if i.val < 7907 then
7341
else
4895))
else
(if i.val < 7910 then
(if i.val < 7909 then
8621
else
4724)
else
(if i.val < 7911 then
8454
else
8464)))
else
(if i.val < 7916 then
(if i.val < 7914 then
(if i.val < 7913 then
4330
else
7205)
else
(if i.val < 7915 then
7741
else
6947))
else
(if i.val < 7918 then
(if i.val < 7917 then
8385
else
6866)
else
(if i.val < 7919 then
6658
else
7169))))
else
(if i.val < 7928 then
(if i.val < 7924 then
(if i.val < 7922 then
(if i.val < 7921 then
4141
else
4329)
else
(if i.val < 7923 then
6249
else
4823))
else
(if i.val < 7926 then
(if i.val < 7925 then
8447
else
3685)
else
(if i.val < 7927 then
7798
else
5742)))
else
(if i.val < 7932 then
(if i.val < 7930 then
(if i.val < 7929 then
7791
else
8173)
else
(if i.val < 7931 then
8572
else
5875))
else
(if i.val < 7934 then
(if i.val < 7933 then
4172
else
7292)
else
(if i.val < 7935 then
7391
else
7393))))))))
else
(if i.val < 8064 then
(if i.val < 8000 then
(if i.val < 7968 then
(if i.val < 7952 then
(if i.val < 7944 then
(if i.val < 7940 then
(if i.val < 7938 then
(if i.val < 7937 then
8409
else
8365)
else
(if i.val < 7939 then
4262
else
4108))
else
(if i.val < 7942 then
(if i.val < 7941 then
8574
else
7966)
else
(if i.val < 7943 then
3655
else
8016)))
else
(if i.val < 7948 then
(if i.val < 7946 then
(if i.val < 7945 then
6739
else
6828)
else
(if i.val < 7947 then
3158
else
4161))
else
(if i.val < 7950 then
(if i.val < 7949 then
4306
else
7415)
else
(if i.val < 7951 then
3308
else
8622))))
else
(if i.val < 7960 then
(if i.val < 7956 then
(if i.val < 7954 then
(if i.val < 7953 then
5825
else
7257)
else
(if i.val < 7955 then
8595
else
7776))
else
(if i.val < 7958 then
(if i.val < 7957 then
7990
else
8307)
else
(if i.val < 7959 then
7764
else
8299)))
else
(if i.val < 7964 then
(if i.val < 7962 then
(if i.val < 7961 then
8325
else
5660)
else
(if i.val < 7963 then
6798
else
5947))
else
(if i.val < 7966 then
(if i.val < 7965 then
7454
else
5925)
else
(if i.val < 7967 then
5773
else
6701)))))
else
(if i.val < 7984 then
(if i.val < 7976 then
(if i.val < 7972 then
(if i.val < 7970 then
(if i.val < 7969 then
4190
else
6913)
else
(if i.val < 7971 then
3691
else
3504))
else
(if i.val < 7974 then
(if i.val < 7973 then
8619
else
8623)
else
(if i.val < 7975 then
4507
else
4506)))
else
(if i.val < 7980 then
(if i.val < 7978 then
(if i.val < 7977 then
3493
else
3376)
else
(if i.val < 7979 then
8606
else
6847))
else
(if i.val < 7982 then
(if i.val < 7981 then
3519
else
6897)
else
(if i.val < 7983 then
8406
else
6761))))
else
(if i.val < 7992 then
(if i.val < 7988 then
(if i.val < 7986 then
(if i.val < 7985 then
6740
else
7352)
else
(if i.val < 7987 then
3638
else
8330))
else
(if i.val < 7990 then
(if i.val < 7989 then
8328
else
5528)
else
(if i.val < 7991 then
8099
else
7401)))
else
(if i.val < 7996 then
(if i.val < 7994 then
(if i.val < 7993 then
7507
else
5503)
else
(if i.val < 7995 then
5118
else
3479))
else
(if i.val < 7998 then
(if i.val < 7997 then
7265
else
3488)
else
(if i.val < 7999 then
3588
else
3590))))))
else
(if i.val < 8032 then
(if i.val < 8016 then
(if i.val < 8008 then
(if i.val < 8004 then
(if i.val < 8002 then
(if i.val < 8001 then
3591
else
8608)
else
(if i.val < 8003 then
4103
else
4159))
else
(if i.val < 8006 then
(if i.val < 8005 then
3604
else
3605)
else
(if i.val < 8007 then
3607
else
5812)))
else
(if i.val < 8012 then
(if i.val < 8010 then
(if i.val < 8009 then
4821
else
8481)
else
(if i.val < 8011 then
3361
else
3364))
else
(if i.val < 8014 then
(if i.val < 8013 then
3446
else
7894)
else
(if i.val < 8015 then
4076
else
8324))))
else
(if i.val < 8024 then
(if i.val < 8020 then
(if i.val < 8018 then
(if i.val < 8017 then
5731
else
8440)
else
(if i.val < 8019 then
8461
else
6174))
else
(if i.val < 8022 then
(if i.val < 8021 then
3455
else
4781)
else
(if i.val < 8023 then
8607
else
8580)))
else
(if i.val < 8028 then
(if i.val < 8026 then
(if i.val < 8025 then
8473
else
5581)
else
(if i.val < 8027 then
6869
else
7242))
else
(if i.val < 8030 then
(if i.val < 8029 then
5883
else
7880)
else
(if i.val < 8031 then
5932
else
3612)))))
else
(if i.val < 8048 then
(if i.val < 8040 then
(if i.val < 8036 then
(if i.val < 8034 then
(if i.val < 8033 then
3625
else
4074)
else
(if i.val < 8035 then
5728
else
4505))
else
(if i.val < 8038 then
(if i.val < 8037 then
8460
else
8582)
else
(if i.val < 8039 then
8600
else
4695)))
else
(if i.val < 8044 then
(if i.val < 8042 then
(if i.val < 8041 then
7195
else
6905)
else
(if i.val < 8043 then
5788
else
8598))
else
(if i.val < 8046 then
(if i.val < 8045 then
8624
else
8583)
else
(if i.val < 8047 then
6731
else
8604))))
else
(if i.val < 8056 then
(if i.val < 8052 then
(if i.val < 8050 then
(if i.val < 8049 then
4791
else
6800)
else
(if i.val < 8051 then
8348
else
7386))
else
(if i.val < 8054 then
(if i.val < 8053 then
3657
else
7516)
else
(if i.val < 8055 then
6918
else
8293)))
else
(if i.val < 8060 then
(if i.val < 8058 then
(if i.val < 8057 then
7853
else
4312)
else
(if i.val < 8059 then
7885
else
8601))
else
(if i.val < 8062 then
(if i.val < 8061 then
4824
else
3162)
else
(if i.val < 8063 then
3166
else
3220)))))))
else
(if i.val < 8128 then
(if i.val < 8096 then
(if i.val < 8080 then
(if i.val < 8072 then
(if i.val < 8068 then
(if i.val < 8066 then
(if i.val < 8065 then
3221
else
3231)
else
(if i.val < 8067 then
3241
else
3242))
else
(if i.val < 8070 then
(if i.val < 8069 then
3247
else
3251)
else
(if i.val < 8071 then
3626
else
3633)))
else
(if i.val < 8076 then
(if i.val < 8074 then
(if i.val < 8073 then
3639
else
3640)
else
(if i.val < 8075 then
3645
else
3652))
else
(if i.val < 8078 then
(if i.val < 8077 then
3659
else
8019)
else
(if i.val < 8079 then
6661
else
7897))))
else
(if i.val < 8088 then
(if i.val < 8084 then
(if i.val < 8082 then
(if i.val < 8081 then
6679
else
5616)
else
(if i.val < 8083 then
7160
else
7172))
else
(if i.val < 8086 then
(if i.val < 8085 then
5592
else
8568)
else
(if i.val < 8087 then
4260
else
3495)))
else
(if i.val < 8092 then
(if i.val < 8090 then
(if i.val < 8089 then
3120
else
8578)
else
(if i.val < 8091 then
6305
else
5620))
else
(if i.val < 8094 then
(if i.val < 8093 then
3333
else
3368)
else
(if i.val < 8095 then
3370
else
3372)))))
else
(if i.val < 8112 then
(if i.val < 8104 then
(if i.val < 8100 then
(if i.val < 8098 then
(if i.val < 8097 then
3458
else
6818)
else
(if i.val < 8099 then
8609
else
7956))
else
(if i.val < 8102 then
(if i.val < 8101 then
5457
else
4075)
else
(if i.val < 8103 then
8015
else
5657)))
else
(if i.val < 8108 then
(if i.val < 8106 then
(if i.val < 8105 then
5491
else
4217)
else
(if i.val < 8107 then
4890
else
7229))
else
(if i.val < 8110 then
(if i.val < 8109 then
7960
else
5504)
else
(if i.val < 8111 then
4297
else
5777))))
else
(if i.val < 8120 then
(if i.val < 8116 then
(if i.val < 8114 then
(if i.val < 8113 then
8579
else
8296)
else
(if i.val < 8115 then
8341
else
8615))
else
(if i.val < 8118 then
(if i.val < 8117 then
8090
else
3385)
else
(if i.val < 8119 then
5939
else
7158)))
else
(if i.val < 8124 then
(if i.val < 8122 then
(if i.val < 8121 then
8123
else
4878)
else
(if i.val < 8123 then
6881
else
8310))
else
(if i.val < 8126 then
(if i.val < 8125 then
6316
else
6819)
else
(if i.val < 8127 then
5762
else
8468))))))
else
(if i.val < 8160 then
(if i.val < 8144 then
(if i.val < 8136 then
(if i.val < 8132 then
(if i.val < 8130 then
(if i.val < 8129 then
7723
else
8469)
else
(if i.val < 8131 then
4176
else
5410))
else
(if i.val < 8134 then
(if i.val < 8133 then
6694
else
4899)
else
(if i.val < 8135 then
8338
else
3678)))
else
(if i.val < 8140 then
(if i.val < 8138 then
(if i.val < 8137 then
6855
else
5163)
else
(if i.val < 8139 then
8369
else
3266))
else
(if i.val < 8142 then
(if i.val < 8141 then
4696
else
5858)
else
(if i.val < 8143 then
3693
else
7011))))
else
(if i.val < 8152 then
(if i.val < 8148 then
(if i.val < 8146 then
(if i.val < 8145 then
6023
else
5406)
else
(if i.val < 8147 then
7009
else
7304))
else
(if i.val < 8150 then
(if i.val < 8149 then
7857
else
7869)
else
(if i.val < 8151 then
7784
else
4885)))
else
(if i.val < 8156 then
(if i.val < 8154 then
(if i.val < 8153 then
8603
else
3273)
else
(if i.val < 8155 then
6958
else
6763))
else
(if i.val < 8158 then
(if i.val < 8157 then
4369
else
8605)
else
(if i.val < 8159 then
3710
else
5861)))))
else
(if i.val < 8176 then
(if i.val < 8168 then
(if i.val < 8164 then
(if i.val < 8162 then
(if i.val < 8161 then
5710
else
3288)
else
(if i.val < 8163 then
3709
else
3708))
else
(if i.val < 8166 then
(if i.val < 8165 then
6664
else
6248)
else
(if i.val < 8167 then
7240
else
5651)))
else
(if i.val < 8172 then
(if i.val < 8170 then
(if i.val < 8169 then
6953
else
6007)
else
(if i.val < 8171 then
7157
else
4983))
else
(if i.val < 8174 then
(if i.val < 8173 then
6300
else
6255)
else
(if i.val < 8175 then
8089
else
7729))))
else
(if i.val < 8184 then
(if i.val < 8180 then
(if i.val < 8178 then
(if i.val < 8177 then
8617
else
8129)
else
(if i.val < 8179 then
3764
else
7194))
else
(if i.val < 8182 then
(if i.val < 8181 then
7910
else
7835)
else
(if i.val < 8183 then
7181
else
7314)))
else
(if i.val < 8188 then
(if i.val < 8186 then
(if i.val < 8185 then
7717
else
3744)
else
(if i.val < 8187 then
8298
else
4154))
else
(if i.val < 8190 then
(if i.val < 8189 then
4152
else
4816)
else
(if i.val < 8191 then
8381
else
7847)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn2Part0016 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 8416 then
(if i.val < 8304 then
(if i.val < 8248 then
(if i.val < 8220 then
(if i.val < 8206 then
(if i.val < 8199 then
(if i.val < 8195 then
(if i.val < 8193 then
6713
else
(if i.val < 8194 then
8486
else
7312))
else
(if i.val < 8197 then
(if i.val < 8196 then
4995
else
8533)
else
(if i.val < 8198 then
8340
else
8611)))
else
(if i.val < 8202 then
(if i.val < 8200 then
8532
else
(if i.val < 8201 then
4667
else
8030))
else
(if i.val < 8204 then
(if i.val < 8203 then
7396
else
8118)
else
(if i.val < 8205 then
5877
else
5895))))
else
(if i.val < 8213 then
(if i.val < 8209 then
(if i.val < 8207 then
4799
else
(if i.val < 8208 then
6200
else
8470))
else
(if i.val < 8211 then
(if i.val < 8210 then
3294
else
5605)
else
(if i.val < 8212 then
5607
else
4815)))
else
(if i.val < 8216 then
(if i.val < 8214 then
4993
else
(if i.val < 8215 then
7204
else
8575))
else
(if i.val < 8218 then
(if i.val < 8217 then
8587
else
5013)
else
(if i.val < 8219 then
7787
else
5136)))))
else
(if i.val < 8234 then
(if i.val < 8227 then
(if i.val < 8223 then
(if i.val < 8221 then
4210
else
(if i.val < 8222 then
4697
else
4373))
else
(if i.val < 8225 then
(if i.val < 8224 then
4415
else
7146)
else
(if i.val < 8226 then
8172
else
7534)))
else
(if i.val < 8230 then
(if i.val < 8228 then
3283
else
(if i.val < 8229 then
3284
else
3292))
else
(if i.val < 8232 then
(if i.val < 8231 then
3310
else
3337)
else
(if i.val < 8233 then
3378
else
3383))))
else
(if i.val < 8241 then
(if i.val < 8237 then
(if i.val < 8235 then
3388
else
(if i.val < 8236 then
3393
else
3517))
else
(if i.val < 8239 then
(if i.val < 8238 then
3680
else
3707)
else
(if i.val < 8240 then
3728
else
3757)))
else
(if i.val < 8244 then
(if i.val < 8242 then
3758
else
(if i.val < 8243 then
4117
else
4119))
else
(if i.val < 8246 then
(if i.val < 8245 then
4135
else
4136)
else
(if i.val < 8247 then
4139
else
4188))))))
else
(if i.val < 8276 then
(if i.val < 8262 then
(if i.val < 8255 then
(if i.val < 8251 then
(if i.val < 8249 then
4189
else
(if i.val < 8250 then
4195
else
4212))
else
(if i.val < 8253 then
(if i.val < 8252 then
4219
else
4225)
else
(if i.val < 8254 then
4228
else
4246)))
else
(if i.val < 8258 then
(if i.val < 8256 then
4252
else
(if i.val < 8257 then
4273
else
4278))
else
(if i.val < 8260 then
(if i.val < 8259 then
7918
else
6670)
else
(if i.val < 8261 then
8309
else
6652))))
else
(if i.val < 8269 then
(if i.val < 8265 then
(if i.val < 8263 then
8463
else
(if i.val < 8264 then
8625
else
8567))
else
(if i.val < 8267 then
(if i.val < 8266 then
4743
else
8626)
else
(if i.val < 8268 then
8319
else
7881)))
else
(if i.val < 8272 then
(if i.val < 8270 then
8314
else
(if i.val < 8271 then
5873
else
7944))
else
(if i.val < 8274 then
(if i.val < 8273 then
7984
else
7898)
else
(if i.val < 8275 then
8475
else
4685)))))
else
(if i.val < 8290 then
(if i.val < 8283 then
(if i.val < 8279 then
(if i.val < 8277 then
7765
else
(if i.val < 8278 then
6849
else
8616))
else
(if i.val < 8281 then
(if i.val < 8280 then
8596
else
7738)
else
(if i.val < 8282 then
5738
else
8327)))
else
(if i.val < 8286 then
(if i.val < 8284 then
8125
else
(if i.val < 8285 then
4504
else
7832))
else
(if i.val < 8288 then
(if i.val < 8287 then
4705
else
8051)
else
(if i.val < 8289 then
4480
else
8474))))
else
(if i.val < 8297 then
(if i.val < 8293 then
(if i.val < 8291 then
4893
else
(if i.val < 8292 then
7349
else
8179))
else
(if i.val < 8295 then
(if i.val < 8294 then
5739
else
8367)
else
(if i.val < 8296 then
4361
else
6683)))
else
(if i.val < 8300 then
(if i.val < 8298 then
8357
else
(if i.val < 8299 then
5787
else
7805))
else
(if i.val < 8302 then
(if i.val < 8301 then
5093
else
8491)
else
(if i.val < 8303 then
8494
else
8627)))))))
else
(if i.val < 8360 then
(if i.val < 8332 then
(if i.val < 8318 then
(if i.val < 8311 then
(if i.val < 8307 then
(if i.val < 8305 then
7873
else
(if i.val < 8306 then
8592
else
8530))
else
(if i.val < 8309 then
(if i.val < 8308 then
8380
else
8404)
else
(if i.val < 8310 then
6680
else
8120)))
else
(if i.val < 8314 then
(if i.val < 8312 then
8040
else
(if i.val < 8313 then
7745
else
8507))
else
(if i.val < 8316 then
(if i.val < 8315 then
6727
else
8304)
else
(if i.val < 8317 then
8526
else
7940))))
else
(if i.val < 8325 then
(if i.val < 8321 then
(if i.val < 8319 then
4370
else
(if i.val < 8320 then
6714
else
8628))
else
(if i.val < 8323 then
(if i.val < 8322 then
7820
else
7936)
else
(if i.val < 8324 then
8344
else
8102)))
else
(if i.val < 8328 then
(if i.val < 8326 then
8108
else
(if i.val < 8327 then
6240
else
6803))
else
(if i.val < 8330 then
(if i.val < 8329 then
8332
else
7846)
else
(if i.val < 8331 then
8591
else
7937)))))
else
(if i.val < 8346 then
(if i.val < 8339 then
(if i.val < 8335 then
(if i.val < 8333 then
7988
else
(if i.val < 8334 then
8297
else
7916))
else
(if i.val < 8337 then
(if i.val < 8336 then
7886
else
7735)
else
(if i.val < 8338 then
5509
else
8405)))
else
(if i.val < 8342 then
(if i.val < 8340 then
8112
else
(if i.val < 8341 then
5908
else
5874))
else
(if i.val < 8344 then
(if i.val < 8343 then
5146
else
5796)
else
(if i.val < 8345 then
8629
else
7973))))
else
(if i.val < 8353 then
(if i.val < 8349 then
(if i.val < 8347 then
7902
else
(if i.val < 8348 then
5465
else
5827))
else
(if i.val < 8351 then
(if i.val < 8350 then
5475
else
8383)
else
(if i.val < 8352 then
8444
else
5445)))
else
(if i.val < 8356 then
(if i.val < 8354 then
8631
else
(if i.val < 8355 then
7783
else
8371))
else
(if i.val < 8358 then
(if i.val < 8357 then
7267
else
8333)
else
(if i.val < 8359 then
8363
else
8355))))))
else
(if i.val < 8388 then
(if i.val < 8374 then
(if i.val < 8367 then
(if i.val < 8363 then
(if i.val < 8361 then
8373
else
(if i.val < 8362 then
8043
else
8593))
else
(if i.val < 8365 then
(if i.val < 8364 then
8632
else
8119)
else
(if i.val < 8366 then
8331
else
5448)))
else
(if i.val < 8370 then
(if i.val < 8368 then
7773
else
(if i.val < 8369 then
5637
else
7236))
else
(if i.val < 8372 then
(if i.val < 8371 then
8581
else
8359)
else
(if i.val < 8373 then
8635
else
8450))))
else
(if i.val < 8381 then
(if i.val < 8377 then
(if i.val < 8375 then
7293
else
(if i.val < 8376 then
7327
else
4453))
else
(if i.val < 8379 then
(if i.val < 8378 then
7310
else
8455)
else
(if i.val < 8380 then
4399
else
7957)))
else
(if i.val < 8384 then
(if i.val < 8382 then
5826
else
(if i.val < 8383 then
7924
else
7381))
else
(if i.val < 8386 then
(if i.val < 8385 then
8519
else
8334)
else
(if i.val < 8387 then
5094
else
4326)))))
else
(if i.val < 8402 then
(if i.val < 8395 then
(if i.val < 8391 then
(if i.val < 8389 then
4465
else
(if i.val < 8390 then
4466
else
4467))
else
(if i.val < 8393 then
(if i.val < 8392 then
4472
else
8594)
else
(if i.val < 8394 then
6663
else
8633)))
else
(if i.val < 8398 then
(if i.val < 8396 then
8472
else
(if i.val < 8397 then
7028
else
4374))
else
(if i.val < 8400 then
(if i.val < 8399 then
4406
else
4867)
else
(if i.val < 8401 then
4686
else
8566))))
else
(if i.val < 8409 then
(if i.val < 8405 then
(if i.val < 8403 then
5573
else
(if i.val < 8404 then
8577
else
8634))
else
(if i.val < 8407 then
(if i.val < 8406 then
8134
else
5741)
else
(if i.val < 8408 then
7215
else
6865)))
else
(if i.val < 8412 then
(if i.val < 8410 then
8322
else
(if i.val < 8411 then
5168
else
6210))
else
(if i.val < 8414 then
(if i.val < 8413 then
6656
else
6840)
else
(if i.val < 8415 then
8154
else
7844))))))))
else
(if i.val < 8528 then
(if i.val < 8472 then
(if i.val < 8444 then
(if i.val < 8430 then
(if i.val < 8423 then
(if i.val < 8419 then
(if i.val < 8417 then
7207
else
(if i.val < 8418 then
8396
else
4296))
else
(if i.val < 8421 then
(if i.val < 8420 then
4342
else
4380)
else
(if i.val < 8422 then
4493
else
4503)))
else
(if i.val < 8426 then
(if i.val < 8424 then
4646
else
(if i.val < 8425 then
4649
else
4664))
else
(if i.val < 8428 then
(if i.val < 8427 then
4674
else
7838)
else
(if i.val < 8429 then
8520
else
6163))))
else
(if i.val < 8437 then
(if i.val < 8433 then
(if i.val < 8431 then
6885
else
(if i.val < 8432 then
4970
else
4967))
else
(if i.val < 8435 then
(if i.val < 8434 then
8524
else
5593)
else
(if i.val < 8436 then
7318
else
8590)))
else
(if i.val < 8440 then
(if i.val < 8438 then
8306
else
(if i.val < 8439 then
8527
else
8571))
else
(if i.val < 8442 then
(if i.val < 8441 then
5768
else
4759)
else
(if i.val < 8443 then
6708
else
8573)))))
else
(if i.val < 8458 then
(if i.val < 8451 then
(if i.val < 8447 then
(if i.val < 8445 then
8620
else
(if i.val < 8446 then
7834
else
8036))
else
(if i.val < 8449 then
(if i.val < 8448 then
8382
else
7770)
else
(if i.val < 8450 then
4858
else
8360)))
else
(if i.val < 8454 then
(if i.val < 8452 then
8636
else
(if i.val < 8453 then
8303
else
4825))
else
(if i.val < 8456 then
(if i.val < 8455 then
8180
else
6991)
else
(if i.val < 8457 then
8610
else
8356))))
else
(if i.val < 8465 then
(if i.val < 8461 then
(if i.val < 8459 then
8477
else
(if i.val < 8460 then
7239
else
8446))
else
(if i.val < 8463 then
(if i.val < 8462 then
8506
else
7799)
else
(if i.val < 8464 then
6691
else
5585)))
else
(if i.val < 8468 then
(if i.val < 8466 then
7855
else
(if i.val < 8467 then
7843
else
8403))
else
(if i.val < 8470 then
(if i.val < 8469 then
6043
else
8177)
else
(if i.val < 8471 then
6027
else
7208))))))
else
(if i.val < 8500 then
(if i.val < 8486 then
(if i.val < 8479 then
(if i.val < 8475 then
(if i.val < 8473 then
7143
else
(if i.val < 8474 then
6290
else
7476))
else
(if i.val < 8477 then
(if i.val < 8476 then
6744
else
7271)
else
(if i.val < 8478 then
7778
else
6995)))
else
(if i.val < 8482 then
(if i.val < 8480 then
5556
else
(if i.val < 8481 then
8370
else
5900))
else
(if i.val < 8484 then
(if i.val < 8483 then
8107
else
5804)
else
(if i.val < 8485 then
7268
else
7321))))
else
(if i.val < 8493 then
(if i.val < 8489 then
(if i.val < 8487 then
5834
else
(if i.val < 8488 then
5432
else
7951))
else
(if i.val < 8491 then
(if i.val < 8490 then
7295
else
8451)
else
(if i.val < 8492 then
8495
else
8576)))
else
(if i.val < 8496 then
(if i.val < 8494 then
8394
else
(if i.val < 8495 then
7187
else
8301))
else
(if i.val < 8498 then
(if i.val < 8497 then
7964
else
5078)
else
(if i.val < 8499 then
6877
else
8630)))))
else
(if i.val < 8514 then
(if i.val < 8507 then
(if i.val < 8503 then
(if i.val < 8501 then
7481
else
(if i.val < 8502 then
4963
else
6859))
else
(if i.val < 8505 then
(if i.val < 8504 then
8291
else
7206)
else
(if i.val < 8506 then
5408
else
8018)))
else
(if i.val < 8510 then
(if i.val < 8508 then
7747
else
(if i.val < 8509 then
8585
else
8407))
else
(if i.val < 8512 then
(if i.val < 8511 then
4755
else
5099)
else
(if i.val < 8513 then
5112
else
8500))))
else
(if i.val < 8521 then
(if i.val < 8517 then
(if i.val < 8515 then
7216
else
(if i.val < 8516 then
7810
else
8637))
else
(if i.val < 8519 then
(if i.val < 8518 then
7220
else
4897)
else
(if i.val < 8520 then
7794
else
7152)))
else
(if i.val < 8524 then
(if i.val < 8522 then
5520
else
(if i.val < 8523 then
8353
else
8492))
else
(if i.val < 8526 then
(if i.val < 8525 then
7175
else
7930)
else
(if i.val < 8527 then
6908
else
7540)))))))
else
(if i.val < 8584 then
(if i.val < 8556 then
(if i.val < 8542 then
(if i.val < 8535 then
(if i.val < 8531 then
(if i.val < 8529 then
7795
else
(if i.val < 8530 then
7274
else
8437))
else
(if i.val < 8533 then
(if i.val < 8532 then
7133
else
5910)
else
(if i.val < 8534 then
5907
else
5128)))
else
(if i.val < 8538 then
(if i.val < 8536 then
7388
else
(if i.val < 8537 then
7531
else
8516))
else
(if i.val < 8540 then
(if i.val < 8539 then
6874
else
5808)
else
(if i.val < 8541 then
5711
else
7322))))
else
(if i.val < 8549 then
(if i.val < 8545 then
(if i.val < 8543 then
7332
else
(if i.val < 8544 then
7497
else
6873))
else
(if i.val < 8547 then
(if i.val < 8546 then
8536
else
4860)
else
(if i.val < 8548 then
4909
else
5172)))
else
(if i.val < 8552 then
(if i.val < 8550 then
5499
else
(if i.val < 8551 then
5527
else
5540))
else
(if i.val < 8554 then
(if i.val < 8553 then
5557
else
8175)
else
(if i.val < 8555 then
8639
else
7818)))))
else
(if i.val < 8570 then
(if i.val < 8563 then
(if i.val < 8559 then
(if i.val < 8557 then
6003
else
(if i.val < 8558 then
8312
else
7319))
else
(if i.val < 8561 then
(if i.val < 8560 then
5921
else
7891)
else
(if i.val < 8562 then
8448
else
7955)))
else
(if i.val < 8566 then
(if i.val < 8564 then
6272
else
(if i.val < 8565 then
8528
else
8462))
else
(if i.val < 8568 then
(if i.val < 8567 then
8612
else
6696)
else
(if i.val < 8569 then
6199
else
5571))))
else
(if i.val < 8577 then
(if i.val < 8573 then
(if i.val < 8571 then
8602
else
(if i.val < 8572 then
8638
else
8525))
else
(if i.val < 8575 then
(if i.val < 8574 then
8597
else
8317)
else
(if i.val < 8576 then
6057
else
8523)))
else
(if i.val < 8580 then
(if i.val < 8578 then
8467
else
(if i.val < 8579 then
8174
else
8339))
else
(if i.val < 8582 then
(if i.val < 8581 then
5938
else
8480)
else
(if i.val < 8583 then
6222
else
7827))))))
else
(if i.val < 8612 then
(if i.val < 8598 then
(if i.val < 8591 then
(if i.val < 8587 then
(if i.val < 8585 then
6756
else
(if i.val < 8586 then
7490
else
8320))
else
(if i.val < 8589 then
(if i.val < 8588 then
6058
else
8465)
else
(if i.val < 8590 then
8466
else
7189)))
else
(if i.val < 8594 then
(if i.val < 8592 then
7987
else
(if i.val < 8593 then
7736
else
6987))
else
(if i.val < 8596 then
(if i.val < 8595 then
6996
else
6132)
else
(if i.val < 8597 then
6782
else
8443))))
else
(if i.val < 8605 then
(if i.val < 8601 then
(if i.val < 8599 then
8361
else
(if i.val < 8600 then
8499
else
8618))
else
(if i.val < 8603 then
(if i.val < 8602 then
5761
else
7801)
else
(if i.val < 8604 then
7840
else
6191)))
else
(if i.val < 8608 then
(if i.val < 8606 then
6258
else
(if i.val < 8607 then
7131
else
5922))
else
(if i.val < 8610 then
(if i.val < 8609 then
6134
else
7842)
else
(if i.val < 8611 then
7854
else
5909)))))
else
(if i.val < 8626 then
(if i.val < 8619 then
(if i.val < 8615 then
(if i.val < 8613 then
8401
else
(if i.val < 8614 then
6762
else
7273))
else
(if i.val < 8617 then
(if i.val < 8616 then
7173
else
6776)
else
(if i.val < 8618 then
7301
else
8038)))
else
(if i.val < 8622 then
(if i.val < 8620 then
7258
else
(if i.val < 8621 then
8351
else
5644))
else
(if i.val < 8624 then
(if i.val < 8623 then
8488
else
8345)
else
(if i.val < 8625 then
7828
else
6692))))
else
(if i.val < 8633 then
(if i.val < 8629 then
(if i.val < 8627 then
6705
else
(if i.val < 8628 then
8452
else
8586))
else
(if i.val < 8631 then
(if i.val < 8630 then
8323
else
8599)
else
(if i.val < 8632 then
8522
else
8358)))
else
(if i.val < 8636 then
(if i.val < 8634 then
8493
else
(if i.val < 8635 then
8308
else
7182))
else
(if i.val < 8638 then
(if i.val < 8637 then
8490
else
8537)
else
(if i.val < 8639 then
8439
else
7730)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0000 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
4
else
16)
else
(if i.val < 3 then
12
else
17))
else
(if i.val < 6 then
(if i.val < 5 then
18
else
52)
else
(if i.val < 7 then
53
else
54)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
29
else
41)
else
(if i.val < 11 then
37
else
42))
else
(if i.val < 14 then
(if i.val < 13 then
43
else
55)
else
(if i.val < 15 then
56
else
50))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
57
else
58)
else
(if i.val < 19 then
0
else
35))
else
(if i.val < 22 then
(if i.val < 21 then
149
else
150)
else
(if i.val < 23 then
122
else
151)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
152
else
90)
else
(if i.val < 27 then
153
else
154))
else
(if i.val < 30 then
(if i.val < 29 then
155
else
89)
else
(if i.val < 31 then
91
else
66)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
121
else
123)
else
(if i.val < 35 then
101
else
110))
else
(if i.val < 38 then
(if i.val < 37 then
111
else
112)
else
(if i.val < 39 then
124
else
125)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
119
else
126)
else
(if i.val < 43 then
127
else
2))
else
(if i.val < 46 then
(if i.val < 45 then
156
else
157)
else
(if i.val < 47 then
145
else
158))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
159
else
144)
else
(if i.val < 51 then
146
else
140))
else
(if i.val < 54 then
(if i.val < 53 then
160
else
161)
else
(if i.val < 55 then
162
else
163)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
164
else
1)
else
(if i.val < 59 then
3
else
321))
else
(if i.val < 62 then
(if i.val < 61 then
207
else
383)
else
(if i.val < 63 then
103
else
384))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
385
else
386)
else
(if i.val < 67 then
245
else
387))
else
(if i.val < 70 then
(if i.val < 69 then
190
else
294)
else
(if i.val < 71 then
322
else
274)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
25
else
388)
else
(if i.val < 75 then
246
else
389))
else
(if i.val < 78 then
(if i.val < 77 then
390
else
391)
else
(if i.val < 79 then
217
else
247))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
186
else
392)
else
(if i.val < 83 then
393
else
394))
else
(if i.val < 86 then
(if i.val < 85 then
395
else
396)
else
(if i.val < 87 then
373
else
250)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
397
else
8)
else
(if i.val < 91 then
72
else
244))
else
(if i.val < 94 then
(if i.val < 93 then
248
else
249)
else
(if i.val < 95 then
185
else
187)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
320
else
21)
else
(if i.val < 99 then
323
else
324))
else
(if i.val < 102 then
(if i.val < 101 then
325
else
273)
else
(if i.val < 103 then
275
else
205)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
293
else
295)
else
(if i.val < 107 then
174
else
296))
else
(if i.val < 110 then
(if i.val < 109 then
297
else
291)
else
(if i.val < 111 then
19
else
298))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
10
else
326)
else
(if i.val < 115 then
327
else
316))
else
(if i.val < 118 then
(if i.val < 117 then
328
else
329)
else
(if i.val < 119 then
315
else
317)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
311
else
330)
else
(if i.val < 123 then
331
else
332))
else
(if i.val < 126 then
(if i.val < 125 then
333
else
334)
else
(if i.val < 127 then
9
else
11)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
398
else
399)
else
(if i.val < 131 then
400
else
401))
else
(if i.val < 134 then
(if i.val < 133 then
375
else
374)
else
(if i.val < 135 then
349
else
363)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
402
else
403)
else
(if i.val < 139 then
404
else
405))
else
(if i.val < 142 then
(if i.val < 141 then
377
else
366)
else
(if i.val < 143 then
367
else
371))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
372
else
376)
else
(if i.val < 147 then
15
else
362))
else
(if i.val < 150 then
(if i.val < 149 then
364
else
406)
else
(if i.val < 151 then
97
else
170)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
407
else
408)
else
(if i.val < 155 then
409
else
410))
else
(if i.val < 158 then
(if i.val < 157 then
411
else
412)
else
(if i.val < 159 then
413
else
382)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
5
else
6)
else
(if i.val < 163 then
7
else
13))
else
(if i.val < 166 then
(if i.val < 165 then
14
else
71)
else
(if i.val < 167 then
783
else
216)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
420
else
906)
else
(if i.val < 171 then
23
else
907))
else
(if i.val < 174 then
(if i.val < 173 then
908
else
909)
else
(if i.val < 175 then
691
else
910))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
475
else
911)
else
(if i.val < 179 then
912
else
913))
else
(if i.val < 182 then
(if i.val < 181 then
914
else
915)
else
(if i.val < 183 then
889
else
916)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
917
else
465)
else
(if i.val < 187 then
199
else
602))
else
(if i.val < 190 then
(if i.val < 189 then
918
else
919)
else
(if i.val < 191 then
193
else
476))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
718
else
68)
else
(if i.val < 195 then
784
else
785))
else
(if i.val < 198 then
(if i.val < 197 then
786
else
494)
else
(if i.val < 199 then
667
else
80)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
920
else
104)
else
(if i.val < 203 then
921
else
922))
else
(if i.val < 206 then
(if i.val < 205 then
923
else
62)
else
(if i.val < 207 then
603
else
466))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
924
else
925)
else
(if i.val < 211 then
926
else
927))
else
(if i.val < 214 then
(if i.val < 213 then
928
else
929)
else
(if i.val < 215 then
606
else
930)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
512
else
539)
else
(if i.val < 219 then
540
else
604))
else
(if i.val < 222 then
(if i.val < 221 then
605
else
438)
else
(if i.val < 223 then
467
else
931)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
932
else
933)
else
(if i.val < 227 then
934
else
935))
else
(if i.val < 230 then
(if i.val < 229 then
936
else
937)
else
(if i.val < 231 then
938
else
939)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
940
else
941)
else
(if i.val < 235 then
942
else
612))
else
(if i.val < 238 then
(if i.val < 237 then
943
else
866)
else
(if i.val < 239 then
886
else
589))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
609
else
470)
else
(if i.val < 243 then
944
else
945))
else
(if i.val < 246 then
(if i.val < 245 then
30
else
31)
else
(if i.val < 247 then
428
else
598)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
599
else
600)
else
(if i.val < 251 then
601
else
607))
else
(if i.val < 254 then
(if i.val < 253 then
608
else
610)
else
(if i.val < 255 then
611
else
168))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
464
else
468)
else
(if i.val < 259 then
469
else
778))
else
(if i.val < 262 then
(if i.val < 261 then
284
else
779)
else
(if i.val < 263 then
780
else
781)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
782
else
787)
else
(if i.val < 267 then
788
else
789))
else
(if i.val < 270 then
(if i.val < 269 then
566
else
790)
else
(if i.val < 271 then
768
else
670))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
544
else
34)
else
(if i.val < 275 then
165
else
666))
else
(if i.val < 278 then
(if i.val < 277 then
668
else
669)
else
(if i.val < 279 then
641
else
717)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
719
else
720)
else
(if i.val < 283 then
721
else
692))
else
(if i.val < 286 then
(if i.val < 285 then
418
else
722)
else
(if i.val < 287 then
723
else
713)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
724
else
725)
else
(if i.val < 291 then
712
else
714))
else
(if i.val < 294 then
(if i.val < 293 then
708
else
201)
else
(if i.val < 295 then
726
else
727)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
728
else
729)
else
(if i.val < 299 then
36
else
791))
else
(if i.val < 302 then
(if i.val < 301 then
439
else
792)
else
(if i.val < 303 then
793
else
770))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
769
else
744)
else
(if i.val < 307 then
758
else
794))
else
(if i.val < 310 then
(if i.val < 309 then
795
else
796)
else
(if i.val < 311 then
797
else
772)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
761
else
762)
else
(if i.val < 315 then
766
else
767))
else
(if i.val < 318 then
(if i.val < 317 then
771
else
40)
else
(if i.val < 319 then
757
else
759))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
798
else
422)
else
(if i.val < 323 then
799
else
800))
else
(if i.val < 326 then
(if i.val < 325 then
801
else
802)
else
(if i.val < 327 then
803
else
804)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
805
else
777)
else
(if i.val < 331 then
32
else
22))
else
(if i.val < 334 then
(if i.val < 333 then
33
else
38)
else
(if i.val < 335 then
39
else
946))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
891
else
947)
else
(if i.val < 339 then
948
else
949))
else
(if i.val < 342 then
(if i.val < 341 then
950
else
951)
else
(if i.val < 343 then
952
else
892)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
893
else
868)
else
(if i.val < 347 then
890
else
884))
else
(if i.val < 350 then
(if i.val < 349 then
835
else
836)
else
(if i.val < 351 then
826
else
867)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
856
else
953)
else
(if i.val < 355 then
954
else
955))
else
(if i.val < 358 then
(if i.val < 357 then
956
else
957)
else
(if i.val < 359 then
958
else
874)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
959
else
960)
else
(if i.val < 363 then
897
else
896))
else
(if i.val < 366 then
(if i.val < 365 then
870
else
873)
else
(if i.val < 367 then
875
else
877))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
878
else
885)
else
(if i.val < 371 then
881
else
887))
else
(if i.val < 374 then
(if i.val < 373 then
49
else
888)
else
(if i.val < 375 then
894
else
895)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
46
else
51)
else
(if i.val < 379 then
860
else
864))
else
(if i.val < 382 then
(if i.val < 381 then
865
else
869)
else
(if i.val < 383 then
48
else
961)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
962
else
963)
else
(if i.val < 387 then
964
else
621))
else
(if i.val < 390 then
(if i.val < 389 then
965
else
966)
else
(if i.val < 391 then
967
else
968)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
969
else
970)
else
(if i.val < 395 then
971
else
972))
else
(if i.val < 398 then
(if i.val < 397 then
973
else
974)
else
(if i.val < 399 then
975
else
976))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
977
else
978)
else
(if i.val < 403 then
979
else
980))
else
(if i.val < 406 then
(if i.val < 405 then
905
else
901)
else
(if i.val < 407 then
20
else
24)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
26
else
27)
else
(if i.val < 411 then
28
else
44))
else
(if i.val < 414 then
(if i.val < 413 then
45
else
47)
else
(if i.val < 415 then
1795
else
1796)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
1797
else
1798)
else
(if i.val < 419 then
260
else
1546))
else
(if i.val < 422 then
(if i.val < 421 then
255
else
1781)
else
(if i.val < 423 then
59
else
2038)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
2039
else
2040)
else
(if i.val < 427 then
176
else
661))
else
(if i.val < 430 then
(if i.val < 429 then
74
else
993)
else
(if i.val < 431 then
2041
else
2042))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
2043
else
2044)
else
(if i.val < 435 then
2045
else
2046))
else
(if i.val < 438 then
(if i.val < 437 then
2047
else
197)
else
(if i.val < 439 then
675
else
1840)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
2048
else
2049)
else
(if i.val < 443 then
1116
else
2050))
else
(if i.val < 446 then
(if i.val < 445 then
2051
else
2052)
else
(if i.val < 447 then
2053
else
1955))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
2010
else
2054)
else
(if i.val < 451 then
2055
else
2056))
else
(if i.val < 454 then
(if i.val < 453 then
2057
else
2058)
else
(if i.val < 455 then
2059
else
2060)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
2061
else
2005)
else
(if i.val < 459 then
1999
else
2006))
else
(if i.val < 462 then
(if i.val < 461 then
2062
else
1119)
else
(if i.val < 463 then
484
else
2063))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
1096
else
94)
else
(if i.val < 467 then
60
else
1386))
else
(if i.val < 470 then
(if i.val < 469 then
1394
else
1395)
else
(if i.val < 471 then
1392
else
2064)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
2065
else
2066)
else
(if i.val < 475 then
806
else
426))
else
(if i.val < 478 then
(if i.val < 477 then
1115
else
1117)
else
(if i.val < 479 then
1118
else
1662)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
493
else
1663)
else
(if i.val < 483 then
1664
else
1665))
else
(if i.val < 486 then
(if i.val < 485 then
1602
else
1799)
else
(if i.val < 487 then
1800
else
1801)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
1802
else
1803)
else
(if i.val < 491 then
1804
else
1549))
else
(if i.val < 494 then
(if i.val < 493 then
1805
else
994)
else
(if i.val < 495 then
437
else
1160))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
1547
else
1548)
else
(if i.val < 499 then
1487
else
1657))
else
(if i.val < 502 then
(if i.val < 501 then
2067
else
2068)
else
(if i.val < 503 then
2069
else
2070)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
2071
else
2072)
else
(if i.val < 507 then
1191
else
2073))
else
(if i.val < 510 then
(if i.val < 509 then
2074
else
2075)
else
(if i.val < 511 then
1399
else
2076)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0001 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
167
else
1396)
else
(if i.val < 515 then
1397
else
1398))
else
(if i.val < 518 then
(if i.val < 517 then
1097
else
2077)
else
(if i.val < 519 then
1045
else
2078)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
2079
else
2080)
else
(if i.val < 523 then
2081
else
2082))
else
(if i.val < 526 then
(if i.val < 525 then
2083
else
2084)
else
(if i.val < 527 then
2085
else
2086))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
2087
else
1406)
else
(if i.val < 531 then
2088
else
2089))
else
(if i.val < 534 then
(if i.val < 533 then
2090
else
1405)
else
(if i.val < 535 then
1402
else
1100)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
2091
else
2092)
else
(if i.val < 539 then
1208
else
78))
else
(if i.val < 542 then
(if i.val < 541 then
1269
else
1270)
else
(if i.val < 543 then
1271
else
1272)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
1400
else
1401)
else
(if i.val < 547 then
1403
else
1404))
else
(if i.val < 550 then
(if i.val < 549 then
1037
else
1038)
else
(if i.val < 551 then
1098
else
1099)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
1292
else
2093)
else
(if i.val < 555 then
1513
else
2094))
else
(if i.val < 558 then
(if i.val < 557 then
2095
else
2096)
else
(if i.val < 559 then
2097
else
2008))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
2098
else
1978)
else
(if i.val < 563 then
2099
else
1997))
else
(if i.val < 566 then
(if i.val < 565 then
1316
else
1413)
else
(if i.val < 567 then
1837
else
2100)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
2101
else
2102)
else
(if i.val < 571 then
2103
else
2104))
else
(if i.val < 574 then
(if i.val < 573 then
2105
else
2106)
else
(if i.val < 575 then
2107
else
2108))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
1969
else
2109)
else
(if i.val < 579 then
1420
else
1414))
else
(if i.val < 582 then
(if i.val < 581 then
1421
else
2110)
else
(if i.val < 583 then
1419
else
1346)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
1958
else
1996)
else
(if i.val < 587 then
1998
else
1364))
else
(if i.val < 590 then
(if i.val < 589 then
1083
else
1367)
else
(if i.val < 591 then
1412
else
1411))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1103
else
1106)
else
(if i.val < 595 then
2111
else
2112))
else
(if i.val < 598 then
(if i.val < 597 then
2113
else
1105)
else
(if i.val < 599 then
79
else
92)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
93
else
87)
else
(if i.val < 603 then
95
else
1383))
else
(if i.val < 606 then
(if i.val < 605 then
1384
else
1385)
else
(if i.val < 607 then
652
else
1387)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
1388
else
1389)
else
(if i.val < 611 then
1390
else
1391))
else
(if i.val < 614 then
(if i.val < 613 then
1393
else
1407)
else
(if i.val < 615 then
1408
else
1409)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1410
else
1415)
else
(if i.val < 619 then
1416
else
1417))
else
(if i.val < 622 then
(if i.val < 621 then
1418
else
67)
else
(if i.val < 623 then
1092
else
1093))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
1094
else
1095)
else
(if i.val < 627 then
1101
else
1102))
else
(if i.val < 630 then
(if i.val < 629 then
1104
else
1782)
else
(if i.val < 631 then
1783
else
1784)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
1785
else
1786)
else
(if i.val < 635 then
1787
else
1788))
else
(if i.val < 638 then
(if i.val < 637 then
1789
else
1790)
else
(if i.val < 639 then
175
else
1791)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
1792
else
1545)
else
(if i.val < 643 then
1793
else
1794))
else
(if i.val < 646 then
(if i.val < 645 then
1494
else
1806)
else
(if i.val < 647 then
1807
else
1808)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
1809
else
538)
else
(if i.val < 651 then
1275
else
1810))
else
(if i.val < 654 then
(if i.val < 653 then
214
else
1811)
else
(if i.val < 655 then
1812
else
1813))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
1814
else
1555)
else
(if i.val < 659 then
1279
else
1743))
else
(if i.val < 662 then
(if i.val < 661 then
1763
else
1533)
else
(if i.val < 663 then
1552
else
1490)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
1815
else
1816)
else
(if i.val < 667 then
102
else
1541))
else
(if i.val < 670 then
(if i.val < 669 then
1542
else
1543)
else
(if i.val < 671 then
1544
else
1550)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
1551
else
1553)
else
(if i.val < 675 then
1554
else
221))
else
(if i.val < 678 then
(if i.val < 677 then
1486
else
1488)
else
(if i.val < 679 then
1489
else
1658)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
1659
else
1660)
else
(if i.val < 683 then
1661
else
1666))
else
(if i.val < 686 then
(if i.val < 685 then
1667
else
1668)
else
(if i.val < 687 then
1510
else
1669))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
1648
else
1605)
else
(if i.val < 691 then
1164
else
106))
else
(if i.val < 694 then
(if i.val < 693 then
1601
else
1603)
else
(if i.val < 695 then
1604
else
1108)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1670
else
1464)
else
(if i.val < 699 then
1671
else
1672))
else
(if i.val < 702 then
(if i.val < 701 then
1650
else
1649)
else
(if i.val < 703 then
1626
else
1639))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
1673
else
1674)
else
(if i.val < 707 then
1675
else
1676))
else
(if i.val < 710 then
(if i.val < 709 then
1652
else
1642)
else
(if i.val < 711 then
1643
else
1646)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
1647
else
1651)
else
(if i.val < 715 then
109
else
1638))
else
(if i.val < 718 then
(if i.val < 717 then
1640
else
1677)
else
(if i.val < 719 then
1678
else
1679))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
1680
else
1681)
else
(if i.val < 723 then
1682
else
1683))
else
(if i.val < 726 then
(if i.val < 725 then
1684
else
1656)
else
(if i.val < 727 then
69
else
105)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
107
else
108)
else
(if i.val < 731 then
1817
else
1767))
else
(if i.val < 734 then
(if i.val < 733 then
1818
else
1041)
else
(if i.val < 735 then
1819
else
340)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1277
else
1820)
else
(if i.val < 739 then
1768
else
1769))
else
(if i.val < 742 then
(if i.val < 741 then
1745
else
1766)
else
(if i.val < 743 then
1761
else
1714)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
1715
else
1705)
else
(if i.val < 747 then
1744
else
1734))
else
(if i.val < 750 then
(if i.val < 749 then
1821
else
1040)
else
(if i.val < 751 then
833
else
1822))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
1823
else
1824)
else
(if i.val < 755 then
1751
else
1825))
else
(if i.val < 758 then
(if i.val < 757 then
1826
else
1773)
else
(if i.val < 759 then
1772
else
1747)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
1750
else
1752)
else
(if i.val < 763 then
1754
else
1755))
else
(if i.val < 766 then
(if i.val < 765 then
1762
else
1758)
else
(if i.val < 767 then
1764
else
118))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
1765
else
1770)
else
(if i.val < 771 then
1771
else
115))
else
(if i.val < 774 then
(if i.val < 773 then
120
else
1738)
else
(if i.val < 775 then
1245
else
1742)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1746
else
117)
else
(if i.val < 779 then
1827
else
1828))
else
(if i.val < 782 then
(if i.val < 781 then
1829
else
1830)
else
(if i.val < 783 then
1561
else
1017))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1831
else
1832)
else
(if i.val < 787 then
1833
else
1834))
else
(if i.val < 790 then
(if i.val < 789 then
1835
else
1836)
else
(if i.val < 791 then
1838
else
1839)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
1841
else
1842)
else
(if i.val < 795 then
825
else
1843))
else
(if i.val < 798 then
(if i.val < 797 then
1780
else
1777)
else
(if i.val < 799 then
96
else
70)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
98
else
99)
else
(if i.val < 803 then
100
else
113))
else
(if i.val < 806 then
(if i.val < 805 then
114
else
116)
else
(if i.val < 807 then
2114
else
2115)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
2116
else
1960)
else
(if i.val < 811 then
1994
else
2007))
else
(if i.val < 814 then
(if i.val < 813 then
2117
else
2118)
else
(if i.val < 815 then
2119
else
2120))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
2121
else
2122)
else
(if i.val < 819 then
2123
else
2124))
else
(if i.val < 822 then
(if i.val < 821 then
2125
else
2011)
else
(if i.val < 823 then
2126
else
2009)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
1993
else
307)
else
(if i.val < 827 then
1904
else
1886))
else
(if i.val < 830 then
(if i.val < 829 then
1961
else
1902)
else
(if i.val < 831 then
1977
else
1986))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
1899
else
1884)
else
(if i.val < 835 then
1059
else
1903))
else
(if i.val < 838 then
(if i.val < 837 then
134
else
1885)
else
(if i.val < 839 then
1876
else
1959)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
1954
else
1938)
else
(if i.val < 843 then
1939
else
1930))
else
(if i.val < 846 then
(if i.val < 845 then
2127
else
2128)
else
(if i.val < 847 then
2129
else
2130))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
2131
else
2132)
else
(if i.val < 851 then
2133
else
2134))
else
(if i.val < 854 then
(if i.val < 853 then
1971
else
2135)
else
(if i.val < 855 then
2136
else
2137)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
2017
else
2138)
else
(if i.val < 859 then
1970
else
1945))
else
(if i.val < 862 then
(if i.val < 861 then
2018
else
2139)
else
(if i.val < 863 then
2140
else
2141)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
2019
else
1965)
else
(if i.val < 867 then
2003
else
2016))
else
(if i.val < 870 then
(if i.val < 869 then
2015
else
1964)
else
(if i.val < 871 then
148
else
1966)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1530
else
1968)
else
(if i.val < 875 then
1972
else
141))
else
(if i.val < 878 then
(if i.val < 877 then
1974
else
142)
else
(if i.val < 879 then
1979
else
1124))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1995
else
1987)
else
(if i.val < 883 then
1983
else
1988))
else
(if i.val < 886 then
(if i.val < 885 then
2000
else
2001)
else
(if i.val < 887 then
2002
else
143)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
86
else
2004)
else
(if i.val < 891 then
2012
else
2013))
else
(if i.val < 894 then
(if i.val < 893 then
2014
else
1905)
else
(if i.val < 895 then
133
else
132)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
135
else
147)
else
(if i.val < 899 then
1948
else
1951))
else
(if i.val < 902 then
(if i.val < 901 then
1956
else
139)
else
(if i.val < 903 then
1957
else
1962)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
1963
else
138)
else
(if i.val < 907 then
2142
else
2143))
else
(if i.val < 910 then
(if i.val < 909 then
2144
else
2145)
else
(if i.val < 911 then
638
else
2146))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
2147
else
2148)
else
(if i.val < 915 then
2149
else
2150))
else
(if i.val < 918 then
(if i.val < 917 then
1439
else
2151)
else
(if i.val < 919 then
1437
else
1438)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
2152
else
2153)
else
(if i.val < 923 then
1756
else
2154))
else
(if i.val < 926 then
(if i.val < 925 then
2155
else
2156)
else
(if i.val < 927 then
2157
else
2158)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
2159
else
2160)
else
(if i.val < 931 then
2161
else
2162))
else
(if i.val < 934 then
(if i.val < 933 then
2163
else
2164)
else
(if i.val < 935 then
2165
else
2166)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
2167
else
2168)
else
(if i.val < 939 then
2169
else
2170))
else
(if i.val < 942 then
(if i.val < 941 then
2171
else
2172)
else
(if i.val < 943 then
2032
else
2173))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
2174
else
2175)
else
(if i.val < 947 then
2176
else
2177))
else
(if i.val < 950 then
(if i.val < 949 then
2178
else
2179)
else
(if i.val < 951 then
735
else
2180)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
2181
else
2182)
else
(if i.val < 955 then
2183
else
2184))
else
(if i.val < 958 then
(if i.val < 957 then
2037
else
2036)
else
(if i.val < 959 then
1914
else
2022))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
2031
else
61)
else
(if i.val < 963 then
63
else
64))
else
(if i.val < 966 then
(if i.val < 965 then
65
else
73)
else
(if i.val < 967 then
75
else
76)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
77
else
81)
else
(if i.val < 971 then
82
else
83))
else
(if i.val < 974 then
(if i.val < 973 then
84
else
85)
else
(if i.val < 975 then
88
else
128))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
129
else
130)
else
(if i.val < 979 then
131
else
136))
else
(if i.val < 982 then
(if i.val < 981 then
137
else
3484)
else
(if i.val < 983 then
3697
else
3698)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
430
else
578)
else
(if i.val < 987 then
3699
else
3700))
else
(if i.val < 990 then
(if i.val < 989 then
2202
else
3701)
else
(if i.val < 991 then
3702
else
3703)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
3276
else
3704)
else
(if i.val < 995 then
480
else
3273))
else
(if i.val < 998 then
(if i.val < 997 then
3274
else
3275)
else
(if i.val < 999 then
594
else
3473)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
3677
else
3678)
else
(if i.val < 1003 then
3679
else
1596))
else
(if i.val < 1006 then
(if i.val < 1005 then
4069
else
4070)
else
(if i.val < 1007 then
4071
else
4072))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
4073
else
4074)
else
(if i.val < 1011 then
4075
else
4076))
else
(if i.val < 1014 then
(if i.val < 1013 then
3283
else
1527)
else
(if i.val < 1015 then
1062
else
2461)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
1030
else
166)
else
(if i.val < 1019 then
2274
else
4077))
else
(if i.val < 1022 then
(if i.val < 1021 then
4078
else
436)
else
(if i.val < 1023 then
1314
else
4079)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0002 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
2209
else
4080)
else
(if i.val < 1027 then
4081
else
4082))
else
(if i.val < 1030 then
(if i.val < 1029 then
4083
else
2020)
else
(if i.val < 1031 then
4084
else
4085)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
4086
else
2463)
else
(if i.val < 1035 then
2306
else
4087))
else
(if i.val < 1038 then
(if i.val < 1037 then
4088
else
1168)
else
(if i.val < 1039 then
2809
else
3417))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
1295
else
3774)
else
(if i.val < 1043 then
2781
else
4089))
else
(if i.val < 1046 then
(if i.val < 1045 then
1846
else
2324)
else
(if i.val < 1047 then
2462
else
2026)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
4033
else
4090)
else
(if i.val < 1051 then
3982
else
4091))
else
(if i.val < 1054 then
(if i.val < 1053 then
3938
else
4092)
else
(if i.val < 1055 then
2504
else
4093)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
3950
else
4094)
else
(if i.val < 1059 then
4019
else
2865))
else
(if i.val < 1062 then
(if i.val < 1061 then
3572
else
2778)
else
(if i.val < 1063 then
3290
else
4095)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
4096
else
1627)
else
(if i.val < 1067 then
3969
else
4097))
else
(if i.val < 1070 then
(if i.val < 1069 then
4098
else
4099)
else
(if i.val < 1071 then
4100
else
4101))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
1268
else
4102)
else
(if i.val < 1075 then
4103
else
1136))
else
(if i.val < 1078 then
(if i.val < 1077 then
4104
else
4027)
else
(if i.val < 1079 then
3955
else
3939)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
4020
else
4028)
else
(if i.val < 1083 then
2393
else
2952))
else
(if i.val < 1086 then
(if i.val < 1085 then
4105
else
4106)
else
(if i.val < 1087 then
2466
else
2469))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
1134
else
3987)
else
(if i.val < 1091 then
4107
else
2468))
else
(if i.val < 1094 then
(if i.val < 1093 then
2412
else
2419)
else
(if i.val < 1095 then
2420
else
2418)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
256
else
1154)
else
(if i.val < 1099 then
2987
else
2988))
else
(if i.val < 1102 then
(if i.val < 1101 then
2985
else
3003)
else
(if i.val < 1103 then
3004
else
3001))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
3005
else
1290)
else
(if i.val < 1107 then
2999
else
4108))
else
(if i.val < 1110 then
(if i.val < 1109 then
3379
else
4109)
else
(if i.val < 1111 then
4110
else
4111)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
4112
else
4113)
else
(if i.val < 1115 then
4114
else
191))
else
(if i.val < 1118 then
(if i.val < 1117 then
1132
else
2458)
else
(if i.val < 1119 then
2459
else
2460)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
2464
else
2465)
else
(if i.val < 1123 then
2467
else
3485))
else
(if i.val < 1126 then
(if i.val < 1125 then
3486
else
3487)
else
(if i.val < 1127 then
3380
else
3488)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
3489
else
3490)
else
(if i.val < 1131 then
3491
else
3492))
else
(if i.val < 1134 then
(if i.val < 1133 then
442
else
3493)
else
(if i.val < 1135 then
2503
else
3381))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
3382
else
3335)
else
(if i.val < 1139 then
3705
else
3131))
else
(if i.val < 1142 then
(if i.val < 1141 then
3706
else
3707)
else
(if i.val < 1143 then
3708
else
3709)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
523
else
3710)
else
(if i.val < 1147 then
3711
else
3712))
else
(if i.val < 1150 then
(if i.val < 1149 then
3713
else
3714)
else
(if i.val < 1151 then
3281
else
1853)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
3715
else
3716)
else
(if i.val < 1155 then
516
else
1890))
else
(if i.val < 1158 then
(if i.val < 1157 then
3172
else
3717)
else
(if i.val < 1159 then
3718
else
2218)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
2559
else
2560)
else
(if i.val < 1163 then
2561
else
2562))
else
(if i.val < 1166 then
(if i.val < 1165 then
3277
else
3278)
else
(if i.val < 1167 then
3279
else
3280))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
548
else
3125)
else
(if i.val < 1171 then
3170
else
3171))
else
(if i.val < 1174 then
(if i.val < 1173 then
3474
else
3475)
else
(if i.val < 1175 then
1193
else
4115)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
2641
else
504)
else
(if i.val < 1179 then
4116
else
2749))
else
(if i.val < 1182 then
(if i.val < 1181 then
499
else
4117)
else
(if i.val < 1183 then
4118
else
3009)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
4119
else
765)
else
(if i.val < 1187 then
2471
else
2615))
else
(if i.val < 1190 then
(if i.val < 1189 then
4120
else
4121)
else
(if i.val < 1191 then
4122
else
2623)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
2624
else
2616)
else
(if i.val < 1195 then
4123
else
4124))
else
(if i.val < 1198 then
(if i.val < 1197 then
2631
else
4125)
else
(if i.val < 1199 then
3015
else
4126))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
1189
else
4127)
else
(if i.val < 1203 then
3014
else
2246))
else
(if i.val < 1206 then
(if i.val < 1205 then
2422
else
4128)
else
(if i.val < 1207 then
4129
else
2653)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
649
else
3006)
else
(if i.val < 1211 then
3007
else
3008))
else
(if i.val < 1214 then
(if i.val < 1213 then
3010
else
3011)
else
(if i.val < 1215 then
3012
else
3013))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
700
else
2421)
else
(if i.val < 1219 then
4130
else
4131))
else
(if i.val < 1222 then
(if i.val < 1221 then
4132
else
2327)
else
(if i.val < 1223 then
4133
else
4134)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
4135
else
4136)
else
(if i.val < 1227 then
4137
else
4138))
else
(if i.val < 1230 then
(if i.val < 1229 then
4139
else
4140)
else
(if i.val < 1231 then
4141
else
4142))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
3019
else
4143)
else
(if i.val < 1235 then
4144
else
4145))
else
(if i.val < 1238 then
(if i.val < 1237 then
4146
else
2326)
else
(if i.val < 1239 then
1852
else
1854)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
3404
else
4147)
else
(if i.val < 1243 then
4148
else
4149))
else
(if i.val < 1246 then
(if i.val < 1245 then
732
else
3026)
else
(if i.val < 1247 then
3020
else
3027)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
4150
else
3023)
else
(if i.val < 1251 then
3024
else
4151))
else
(if i.val < 1254 then
(if i.val < 1253 then
4152
else
4153)
else
(if i.val < 1255 then
3025
else
2428)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
2780
else
3018)
else
(if i.val < 1259 then
2425
else
2429))
else
(if i.val < 1262 then
(if i.val < 1261 then
3826
else
4154)
else
(if i.val < 1263 then
4155
else
4156))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
2427
else
2657)
else
(if i.val < 1267 then
2658
else
2659))
else
(if i.val < 1270 then
(if i.val < 1269 then
2604
else
218)
else
(if i.val < 1271 then
2772
else
2773)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
2774
else
2775)
else
(if i.val < 1275 then
2776
else
2777))
else
(if i.val < 1278 then
(if i.val < 1277 then
2779
else
3016)
else
(if i.val < 1279 then
3017
else
1883))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
3021
else
3022)
else
(if i.val < 1283 then
2259
else
2313))
else
(if i.val < 1286 then
(if i.val < 1285 then
2314
else
2315)
else
(if i.val < 1287 then
2316
else
2423)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
2424
else
2426)
else
(if i.val < 1291 then
597
else
2816))
else
(if i.val < 1294 then
(if i.val < 1293 then
2817
else
4157)
else
(if i.val < 1295 then
4014
else
749))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
3220
else
4158)
else
(if i.val < 1299 then
4159
else
4160))
else
(if i.val < 1302 then
(if i.val < 1301 then
4161
else
4162)
else
(if i.val < 1303 then
4163
else
4164)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
4165
else
4166)
else
(if i.val < 1307 then
4018
else
2849))
else
(if i.val < 1310 then
(if i.val < 1309 then
2806
else
4167)
else
(if i.val < 1311 then
4168
else
2703)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
2506
else
2893)
else
(if i.val < 1315 then
2785
else
2821))
else
(if i.val < 1318 then
(if i.val < 1317 then
2352
else
2351)
else
(if i.val < 1319 then
2435
else
4169)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
4170
else
4171)
else
(if i.val < 1323 then
4172
else
4173))
else
(if i.val < 1326 then
(if i.val < 1325 then
4174
else
4175)
else
(if i.val < 1327 then
4176
else
3914))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
4177
else
3581)
else
(if i.val < 1331 then
4178
else
3255))
else
(if i.val < 1334 then
(if i.val < 1333 then
4179
else
4180)
else
(if i.val < 1335 then
4181
else
4182)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
3036
else
3851)
else
(if i.val < 1339 then
3421
else
4183))
else
(if i.val < 1342 then
(if i.val < 1341 then
1422
else
3971)
else
(if i.val < 1343 then
4184
else
4185))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
3046
else
3047)
else
(if i.val < 1347 then
2951
else
3035))
else
(if i.val < 1350 then
(if i.val < 1349 then
2928
else
3048)
else
(if i.val < 1351 then
2442
else
747)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
3045
else
3043)
else
(if i.val < 1355 then
2440
else
2374))
else
(if i.val < 1358 then
(if i.val < 1357 then
2911
else
3956)
else
(if i.val < 1359 then
4017
else
2946))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
3892
else
4004)
else
(if i.val < 1363 then
2945
else
2944))
else
(if i.val < 1366 then
(if i.val < 1365 then
2947
else
2391)
else
(if i.val < 1367 then
682
else
239)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
3034
else
3028)
else
(if i.val < 1371 then
2954
else
3033))
else
(if i.val < 1374 then
(if i.val < 1373 then
2434
else
639)
else
(if i.val < 1375 then
2441
else
2813)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
3790
else
4186)
else
(if i.val < 1379 then
2439
else
3861))
else
(if i.val < 1382 then
(if i.val < 1381 then
4187
else
4188)
else
(if i.val < 1383 then
2438
else
206)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
219
else
220)
else
(if i.val < 1387 then
222
else
251))
else
(if i.val < 1390 then
(if i.val < 1389 then
252
else
240)
else
(if i.val < 1391 then
253
else
254))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
241
else
235)
else
(if i.val < 1395 then
257
else
258))
else
(if i.val < 1398 then
(if i.val < 1397 then
2761
else
2980)
else
(if i.val < 1399 then
2981
else
2982)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
272
else
2983)
else
(if i.val < 1403 then
1511
else
2984))
else
(if i.val < 1406 then
(if i.val < 1405 then
1519
else
1537)
else
(if i.val < 1407 then
2986
else
2989)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
2990
else
2991)
else
(if i.val < 1411 then
2992
else
2908))
else
(if i.val < 1414 then
(if i.val < 1413 then
2956
else
2993)
else
(if i.val < 1415 then
2994
else
2995)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
2996
else
2997)
else
(if i.val < 1419 then
2998
else
3000))
else
(if i.val < 1422 then
(if i.val < 1421 then
985
else
3002)
else
(if i.val < 1423 then
2331
else
2528))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
3029
else
1347)
else
(if i.val < 1427 then
3030
else
3031))
else
(if i.val < 1430 then
(if i.val < 1429 then
3032
else
3037)
else
(if i.val < 1431 then
3038
else
3039)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
3040
else
3041)
else
(if i.val < 1435 then
3042
else
2921))
else
(if i.val < 1438 then
(if i.val < 1437 then
3044
else
188)
else
(if i.val < 1439 then
189
else
183)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
2409
else
2410)
else
(if i.val < 1443 then
2411
else
1145))
else
(if i.val < 1446 then
(if i.val < 1445 then
2413
else
2414)
else
(if i.val < 1447 then
2415
else
2416)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
2417
else
1918)
else
(if i.val < 1451 then
2430
else
2431))
else
(if i.val < 1454 then
(if i.val < 1453 then
2432
else
2433)
else
(if i.val < 1455 then
2436
else
2437))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
2483
else
3680)
else
(if i.val < 1459 then
3681
else
1980))
else
(if i.val < 1462 then
(if i.val < 1461 then
3682
else
3683)
else
(if i.val < 1463 then
3684
else
3685)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
3525
else
3686)
else
(if i.val < 1467 then
3687
else
2791))
else
(if i.val < 1470 then
(if i.val < 1469 then
1256
else
1039)
else
(if i.val < 1471 then
3688
else
2295))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
2793
else
3689)
else
(if i.val < 1475 then
1274
else
857))
else
(if i.val < 1478 then
(if i.val < 1477 then
3690
else
441)
else
(if i.val < 1479 then
3691
else
3692)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
440
else
3647)
else
(if i.val < 1483 then
3652
else
3693))
else
(if i.val < 1486 then
(if i.val < 1485 then
3184
else
3694)
else
(if i.val < 1487 then
3169
else
3263))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
3271
else
3272)
else
(if i.val < 1491 then
3269
else
3695))
else
(if i.val < 1494 then
(if i.val < 1493 then
3696
else
1685)
else
(if i.val < 1495 then
3181
else
3182)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
3183
else
2782)
else
(if i.val < 1499 then
435
else
3353))
else
(if i.val < 1502 then
(if i.val < 1501 then
3719
else
3720)
else
(if i.val < 1503 then
1266
else
3721)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
1250
else
3722)
else
(if i.val < 1507 then
3630
else
2318))
else
(if i.val < 1510 then
(if i.val < 1509 then
1036
else
1311)
else
(if i.val < 1511 then
3523
else
534)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
3723
else
3724)
else
(if i.val < 1515 then
3725
else
1893))
else
(if i.val < 1518 then
(if i.val < 1517 then
1267
else
2788)
else
(if i.val < 1519 then
3726
else
547))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
3621
else
3727)
else
(if i.val < 1523 then
3292
else
3288))
else
(if i.val < 1526 then
(if i.val < 1525 then
3293
else
1940)
else
(if i.val < 1527 then
3291
else
3233)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
2766
else
1273)
else
(if i.val < 1531 then
3646
else
3247))
else
(if i.val < 1534 then
(if i.val < 1533 then
3160
else
427)
else
(if i.val < 1535 then
3287
else
3286)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0003 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
3177
else
533)
else
(if i.val < 1539 then
3728
else
3729))
else
(if i.val < 1542 then
(if i.val < 1541 then
3176
else
198)
else
(if i.val < 1543 then
276
else
277)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
271
else
278)
else
(if i.val < 1547 then
3260
else
3261))
else
(if i.val < 1550 then
(if i.val < 1549 then
3262
else
1587)
else
(if i.val < 1551 then
3264
else
3265))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
3266
else
3267)
else
(if i.val < 1555 then
3268
else
3270))
else
(if i.val < 1558 then
(if i.val < 1557 then
3282
else
3284)
else
(if i.val < 1559 then
3285
else
1880)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
3289
else
264)
else
(if i.val < 1563 then
536
else
3167))
else
(if i.val < 1566 then
(if i.val < 1565 then
3168
else
472)
else
(if i.val < 1567 then
3173
else
3174)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
3175
else
3476)
else
(if i.val < 1571 then
3477
else
3478))
else
(if i.val < 1574 then
(if i.val < 1573 then
841
else
3479)
else
(if i.val < 1575 then
632
else
3480)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
3481
else
3482)
else
(if i.val < 1579 then
3483
else
3339))
else
(if i.val < 1582 then
(if i.val < 1581 then
3494
else
3495)
else
(if i.val < 1583 then
3496
else
3497))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
1159
else
2565)
else
(if i.val < 1587 then
3498
else
491))
else
(if i.val < 1590 then
(if i.val < 1589 then
3499
else
3500)
else
(if i.val < 1591 then
3501
else
3502)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
2608
else
2571)
else
(if i.val < 1595 then
3444
else
3460))
else
(if i.val < 1598 then
(if i.val < 1597 then
3370
else
3385)
else
(if i.val < 1599 then
2445
else
1946))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
3503
else
283)
else
(if i.val < 1603 then
462
else
3376))
else
(if i.val < 1606 then
(if i.val < 1605 then
3377
else
3378)
else
(if i.val < 1607 then
3383
else
3384)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
3386
else
3387)
else
(if i.val < 1611 then
3334
else
3336))
else
(if i.val < 1614 then
(if i.val < 1613 then
2451
else
3504)
else
(if i.val < 1615 then
3464
else
3505))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
3128
else
3506)
else
(if i.val < 1619 then
2569
else
3507))
else
(if i.val < 1622 then
(if i.val < 1621 then
3465
else
452)
else
(if i.val < 1623 then
3446
else
3463)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
3458
else
3419)
else
(if i.val < 1627 then
3420
else
3415))
else
(if i.val < 1630 then
(if i.val < 1629 then
3445
else
3508)
else
(if i.val < 1631 then
3127
else
1712)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
3509
else
3510)
else
(if i.val < 1635 then
3511
else
3451))
else
(if i.val < 1638 then
(if i.val < 1637 then
3512
else
3513)
else
(if i.val < 1639 then
3467
else
3466)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
3448
else
1913)
else
(if i.val < 1643 then
3452
else
3453))
else
(if i.val < 1646 then
(if i.val < 1645 then
3454
else
3459)
else
(if i.val < 1647 then
3461
else
290))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
3462
else
2647)
else
(if i.val < 1651 then
1216
else
287))
else
(if i.val < 1654 then
(if i.val < 1653 then
292
else
3440)
else
(if i.val < 1655 then
2537
else
3447)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
289
else
1180)
else
(if i.val < 1659 then
3514
else
3515))
else
(if i.val < 1662 then
(if i.val < 1661 then
3516
else
1366)
else
(if i.val < 1663 then
3106
else
3517)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
3518
else
3519)
else
(if i.val < 1667 then
3520
else
3521))
else
(if i.val < 1670 then
(if i.val < 1669 then
3522
else
2277)
else
(if i.val < 1671 then
3524
else
1889)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
1863
else
1704)
else
(if i.val < 1675 then
3526
else
3472))
else
(if i.val < 1678 then
(if i.val < 1677 then
3470
else
279)
else
(if i.val < 1679 then
192
else
280))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
281
else
282)
else
(if i.val < 1683 then
285
else
286))
else
(if i.val < 1686 then
(if i.val < 1685 then
288
else
2924)
else
(if i.val < 1687 then
1257
else
3730)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
2744
else
3644)
else
(if i.val < 1691 then
3653
else
3731))
else
(if i.val < 1694 then
(if i.val < 1693 then
3732
else
3733)
else
(if i.val < 1695 then
3734
else
815)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
3735
else
556)
else
(if i.val < 1699 then
2319
else
820))
else
(if i.val < 1702 then
(if i.val < 1701 then
3655
else
3736)
else
(if i.val < 1703 then
3654
else
3643)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
704
else
3576)
else
(if i.val < 1707 then
3561
else
445))
else
(if i.val < 1710 then
(if i.val < 1709 then
3574
else
3629)
else
(if i.val < 1711 then
3637
else
3571))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
3559
else
3141)
else
(if i.val < 1715 then
3575
else
305))
else
(if i.val < 1718 then
(if i.val < 1717 then
3560
else
3552)
else
(if i.val < 1719 then
1031
else
2726)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
3604
else
3598)
else
(if i.val < 1723 then
3737
else
2353))
else
(if i.val < 1726 then
(if i.val < 1725 then
3738
else
1901)
else
(if i.val < 1727 then
1337
else
1315))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
1907
else
3739)
else
(if i.val < 1731 then
3623
else
3740))
else
(if i.val < 1734 then
(if i.val < 1733 then
3741
else
858)
else
(if i.val < 1735 then
1351
else
3742)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
3622
else
3609)
else
(if i.val < 1739 then
3661
else
2897))
else
(if i.val < 1742 then
(if i.val < 1741 then
3743
else
3744)
else
(if i.val < 1743 then
2021
else
3651))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
3660
else
3659)
else
(if i.val < 1747 then
3617
else
319))
else
(if i.val < 1750 then
(if i.val < 1749 then
3618
else
2734)
else
(if i.val < 1751 then
3620
else
3624)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
312
else
3626)
else
(if i.val < 1755 then
313
else
3631))
else
(if i.val < 1758 then
(if i.val < 1757 then
203
else
3645)
else
(if i.val < 1759 then
1185
else
3634)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
3638
else
3648)
else
(if i.val < 1763 then
3649
else
3650))
else
(if i.val < 1766 then
(if i.val < 1765 then
314
else
270)
else
(if i.val < 1767 then
3656
else
3657)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
3658
else
3577)
else
(if i.val < 1771 then
304
else
303))
else
(if i.val < 1774 then
(if i.val < 1773 then
306
else
318)
else
(if i.val < 1775 then
2030
else
2730))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
3614
else
310)
else
(if i.val < 1779 then
3615
else
3616))
else
(if i.val < 1782 then
(if i.val < 1781 then
309
else
3745)
else
(if i.val < 1783 then
3746
else
3747)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
3748
else
1574)
else
(if i.val < 1787 then
3749
else
3750))
else
(if i.val < 1790 then
(if i.val < 1789 then
3751
else
3752)
else
(if i.val < 1791 then
3753
else
1373))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
3754
else
3306)
else
(if i.val < 1795 then
3307
else
3755))
else
(if i.val < 1798 then
(if i.val < 1797 then
3756
else
2287)
else
(if i.val < 1799 then
2271
else
3757)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
3758
else
3759)
else
(if i.val < 1803 then
3760
else
3761))
else
(if i.val < 1806 then
(if i.val < 1805 then
3762
else
3081)
else
(if i.val < 1807 then
3763
else
3764))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
3765
else
3766)
else
(if i.val < 1811 then
3767
else
3768))
else
(if i.val < 1814 then
(if i.val < 1813 then
3769
else
3770)
else
(if i.val < 1815 then
3672
else
3771)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
3772
else
3773)
else
(if i.val < 1819 then
1244
else
3775))
else
(if i.val < 1822 then
(if i.val < 1821 then
3776
else
1881)
else
(if i.val < 1823 then
3676
else
1875)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
3583
else
3664)
else
(if i.val < 1827 then
3671
else
259))
else
(if i.val < 1830 then
(if i.val < 1829 then
261
else
262)
else
(if i.val < 1831 then
263
else
194)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
195
else
196)
else
(if i.val < 1835 then
265
else
266))
else
(if i.val < 1838 then
(if i.val < 1837 then
267
else
268)
else
(if i.val < 1839 then
269
else
299))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
300
else
301)
else
(if i.val < 1843 then
302
else
308))
else
(if i.val < 1846 then
(if i.val < 1845 then
4189
else
3256)
else
(if i.val < 1847 then
3214
else
4190)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
4191
else
4192)
else
(if i.val < 1851 then
4030
else
4031))
else
(if i.val < 1854 then
(if i.val < 1853 then
3878
else
4193)
else
(if i.val < 1855 then
4194
else
4195))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
4196
else
4197)
else
(if i.val < 1859 then
4198
else
2452))
else
(if i.val < 1862 then
(if i.val < 1861 then
3554
else
4199)
else
(if i.val < 1863 then
4200
else
699)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
3550
else
4201)
else
(if i.val < 1867 then
4202
else
4203))
else
(if i.val < 1870 then
(if i.val < 1869 then
2507
else
4032)
else
(if i.val < 1871 then
4204
else
3391))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
4205
else
1864)
else
(if i.val < 1875 then
4206
else
752))
else
(if i.val < 1878 then
(if i.val < 1877 then
3880
else
3957)
else
(if i.val < 1879 then
1860
else
4207)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
3999
else
748)
else
(if i.val < 1883 then
3854
else
658))
else
(if i.val < 1886 then
(if i.val < 1885 then
750
else
3225)
else
(if i.val < 1887 then
3855
else
3856)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
2497
else
698)
else
(if i.val < 1891 then
3352
else
4029))
else
(if i.val < 1894 then
(if i.val < 1893 then
1625
else
3853)
else
(if i.val < 1895 then
3877
else
3116)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
3867
else
3993)
else
(if i.val < 1899 then
2354
else
2203))
else
(if i.val < 1902 then
(if i.val < 1901 then
3863
else
3781)
else
(if i.val < 1903 then
3879
else
348))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
350
else
344)
else
(if i.val < 1907 then
3840
else
3839))
else
(if i.val < 1910 then
(if i.val < 1909 then
3927
else
3943)
else
(if i.val < 1911 then
3925
else
3916)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
2366
else
3928)
else
(if i.val < 1915 then
358
else
3917))
else
(if i.val < 1918 then
(if i.val < 1917 then
4208
else
4209)
else
(if i.val < 1919 then
4210
else
3973)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
4211
else
1190)
else
(if i.val < 1923 then
4212
else
4213))
else
(if i.val < 1926 then
(if i.val < 1925 then
3063
else
4214)
else
(if i.val < 1927 then
4215
else
4216)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
4217
else
1911)
else
(if i.val < 1931 then
4040
else
1709))
else
(if i.val < 1934 then
(if i.val < 1933 then
1569
else
3327)
else
(if i.val < 1935 then
4218
else
4219))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
4220
else
4221)
else
(if i.val < 1939 then
1572
else
3961))
else
(if i.val < 1942 then
(if i.val < 1941 then
4222
else
4223)
else
(if i.val < 1943 then
3972
else
3968)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
3932
else
3933)
else
(if i.val < 1947 then
2671
else
4224))
else
(if i.val < 1950 then
(if i.val < 1949 then
3962
else
4225)
else
(if i.val < 1951 then
4226
else
4042)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
4227
else
4228)
else
(if i.val < 1955 then
4039
else
4041))
else
(if i.val < 1958 then
(if i.val < 1957 then
3963
else
3953)
else
(if i.val < 1959 then
3985
else
4038)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
4034
else
3126)
else
(if i.val < 1963 then
3663
else
3960))
else
(if i.val < 1966 then
(if i.val < 1965 then
381
else
380)
else
(if i.val < 1967 then
3965
else
3966))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
365
else
3970)
else
(if i.val < 1971 then
1733
else
3974))
else
(if i.val < 1974 then
(if i.val < 1973 then
359
else
3983)
else
(if i.val < 1975 then
2210
else
3975)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
2190
else
2214)
else
(if i.val < 1979 then
3984
else
368))
else
(if i.val < 1982 then
(if i.val < 1981 then
3986
else
2405)
else
(if i.val < 1983 then
4015
else
4001))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
3995
else
4016)
else
(if i.val < 1987 then
4000
else
370))
else
(if i.val < 1990 then
(if i.val < 1989 then
4002
else
3994)
else
(if i.val < 1991 then
2690
else
4003)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
4005
else
4021)
else
(if i.val < 1995 then
4022
else
4007))
else
(if i.val < 1998 then
(if i.val < 1997 then
4023
else
4024)
else
(if i.val < 1999 then
3450
else
4025))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
347
else
369)
else
(if i.val < 2003 then
238
else
237))
else
(if i.val < 2006 then
(if i.val < 2005 then
182
else
4026)
else
(if i.val < 2007 then
2950
else
4035)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
2226
else
4036)
else
(if i.val < 2011 then
4037
else
3882))
else
(if i.val < 2014 then
(if i.val < 2013 then
346
else
336)
else
(if i.val < 2015 then
343
else
345)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
351
else
352)
else
(if i.val < 2019 then
378
else
379))
else
(if i.val < 2022 then
(if i.val < 2021 then
3935
else
775)
else
(if i.val < 2023 then
360
else
3940)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
3949
else
3944)
else
(if i.val < 2027 then
2496
else
3945))
else
(if i.val < 2030 then
(if i.val < 2029 then
3670
else
3951)
else
(if i.val < 2031 then
3952
else
361))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
234
else
3954)
else
(if i.val < 2035 then
3958
else
3959))
else
(if i.val < 2038 then
(if i.val < 2037 then
357
else
356)
else
(if i.val < 2039 then
4229
else
4230)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
4231
else
984)
else
(if i.val < 2043 then
4232
else
4233))
else
(if i.val < 2046 then
(if i.val < 2045 then
4234
else
4235)
else
(if i.val < 2047 then
1498
else
1021)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0004 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
1480
else
1477)
else
(if i.val < 2051 then
4236
else
2241))
else
(if i.val < 2054 then
(if i.val < 2053 then
1707
else
4237)
else
(if i.val < 2055 then
4238
else
4239)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
4240
else
1621)
else
(if i.val < 2059 then
4241
else
4062))
else
(if i.val < 2062 then
(if i.val < 2061 then
3078
else
3599)
else
(if i.val < 2063 then
3076
else
4242))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
3075
else
1565)
else
(if i.val < 2067 then
3077
else
4243))
else
(if i.val < 2070 then
(if i.val < 2069 then
4244
else
4245)
else
(if i.val < 2071 then
4246
else
1177)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
4247
else
4248)
else
(if i.val < 2075 then
4249
else
4250))
else
(if i.val < 2078 then
(if i.val < 2077 then
2580
else
4251)
else
(if i.val < 2079 then
4252
else
4253)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
4254
else
4255)
else
(if i.val < 2083 then
1144
else
4256))
else
(if i.val < 2086 then
(if i.val < 2085 then
4257
else
4258)
else
(if i.val < 2087 then
4259
else
3668)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
4260
else
4261)
else
(if i.val < 2091 then
4262
else
1562))
else
(if i.val < 2094 then
(if i.val < 2093 then
4263
else
4264)
else
(if i.val < 2095 then
4265
else
1697))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
4266
else
4267)
else
(if i.val < 2099 then
4268
else
4269))
else
(if i.val < 2102 then
(if i.val < 2101 then
3563
else
4270)
else
(if i.val < 2103 then
3344
else
4271)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
4272
else
4273)
else
(if i.val < 2107 then
4274
else
2541))
else
(if i.val < 2110 then
(if i.val < 2109 then
4275
else
4061)
else
(if i.val < 2111 then
4276
else
998))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
4277
else
4278)
else
(if i.val < 2115 then
474
else
4279))
else
(if i.val < 2118 then
(if i.val < 2117 then
3098
else
2532)
else
(if i.val < 2119 then
4280
else
4281)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
1695
else
3788)
else
(if i.val < 2123 then
4282
else
4283))
else
(if i.val < 2126 then
(if i.val < 2125 then
4284
else
1699)
else
(if i.val < 2127 then
4285
else
4286))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
4067
else
4287)
else
(if i.val < 2131 then
4288
else
4289))
else
(if i.val < 2134 then
(if i.val < 2133 then
4290
else
4068)
else
(if i.val < 2135 then
3897
else
4066)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
4059
else
3896)
else
(if i.val < 2139 then
1475
else
4045))
else
(if i.val < 2142 then
(if i.val < 2141 then
4060
else
4049)
else
(if i.val < 2143 then
169
else
171)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
172
else
173)
else
(if i.val < 2147 then
177
else
178))
else
(if i.val < 2150 then
(if i.val < 2149 then
179
else
180)
else
(if i.val < 2151 then
181
else
184)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
200
else
202)
else
(if i.val < 2155 then
204
else
208))
else
(if i.val < 2158 then
(if i.val < 2157 then
209
else
210)
else
(if i.val < 2159 then
211
else
212))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
213
else
215)
else
(if i.val < 2163 then
223
else
224))
else
(if i.val < 2166 then
(if i.val < 2165 then
225
else
226)
else
(if i.val < 2167 then
227
else
228)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
229
else
230)
else
(if i.val < 2171 then
231
else
232))
else
(if i.val < 2174 then
(if i.val < 2173 then
233
else
236)
else
(if i.val < 2175 then
242
else
243)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
335
else
337)
else
(if i.val < 2179 then
338
else
339))
else
(if i.val < 2182 then
(if i.val < 2181 then
341
else
342)
else
(if i.val < 2183 then
353
else
354)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
355
else
6026)
else
(if i.val < 2187 then
5319
else
1457))
else
(if i.val < 2190 then
(if i.val < 2189 then
1522
else
2272)
else
(if i.val < 2191 then
4335
else
986))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
6245
else
1025)
else
(if i.val < 2195 then
6246
else
1344))
else
(if i.val < 2198 then
(if i.val < 2197 then
2942
else
1352)
else
(if i.val < 2199 then
5670
else
4316)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
1020
else
5211)
else
(if i.val < 2203 then
4320
else
832))
else
(if i.val < 2206 then
(if i.val < 2205 then
6247
else
6248)
else
(if i.val < 2207 then
4326
else
6249)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
5790
else
6250)
else
(if i.val < 2211 then
876
else
2305))
else
(if i.val < 2214 then
(if i.val < 2213 then
1440
else
4365)
else
(if i.val < 2215 then
830
else
6251)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
3062
else
4341)
else
(if i.val < 2219 then
1584
else
5785))
else
(if i.val < 2222 then
(if i.val < 2221 then
5786
else
1005)
else
(if i.val < 2223 then
5442
else
5787))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
5788
else
5789)
else
(if i.val < 2227 then
559
else
2925))
else
(if i.val < 2230 then
(if i.val < 2229 then
6018
else
6019)
else
(if i.val < 2231 then
6212
else
6213)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
6214
else
6215)
else
(if i.val < 2235 then
6216
else
6217))
else
(if i.val < 2238 then
(if i.val < 2237 then
6218
else
6219)
else
(if i.val < 2239 then
5933
else
3365))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
3142
else
444)
else
(if i.val < 2243 then
6645
else
5644))
else
(if i.val < 2246 then
(if i.val < 2245 then
6334
else
6646)
else
(if i.val < 2247 then
5405
else
6647)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
6648
else
6649)
else
(if i.val < 2251 then
6650
else
6478))
else
(if i.val < 2254 then
(if i.val < 2253 then
3910
else
5994)
else
(if i.val < 2255 then
6651
else
5808))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
4406
else
6542)
else
(if i.val < 2259 then
6652
else
5416))
else
(if i.val < 2262 then
(if i.val < 2261 then
1557
else
5800)
else
(if i.val < 2263 then
5796
else
3249)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
3304
else
1991)
else
(if i.val < 2267 then
1624
else
1582))
else
(if i.val < 2270 then
(if i.val < 2269 then
1947
else
6653)
else
(if i.val < 2271 then
2847
else
417)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
4301
else
4429)
else
(if i.val < 2275 then
4430
else
6654))
else
(if i.val < 2278 then
(if i.val < 2277 then
6655
else
687)
else
(if i.val < 2279 then
982
else
2301)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
991
else
2857)
else
(if i.val < 2283 then
2863
else
5817))
else
(if i.val < 2286 then
(if i.val < 2285 then
2194
else
6244)
else
(if i.val < 2287 then
2294
else
416))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
3876
else
6656)
else
(if i.val < 2291 then
1028
else
3203))
else
(if i.val < 2294 then
(if i.val < 2293 then
6657
else
6658)
else
(if i.val < 2295 then
6659
else
5467)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
6660
else
6661)
else
(if i.val < 2299 then
4462
else
6662))
else
(if i.val < 2302 then
(if i.val < 2301 then
3964
else
4425)
else
(if i.val < 2303 then
5942
else
4697))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
4695
else
4441)
else
(if i.val < 2307 then
4300
else
4474))
else
(if i.val < 2310 then
(if i.val < 2309 then
6663
else
4696)
else
(if i.val < 2311 then
6489
else
5023)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
1374
else
4510)
else
(if i.val < 2315 then
4935
else
2333))
else
(if i.val < 2318 then
(if i.val < 2317 then
5186
else
6664)
else
(if i.val < 2319 then
5146
else
5457))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
6665
else
2822)
else
(if i.val < 2323 then
4925
else
4420))
else
(if i.val < 2326 then
(if i.val < 2325 then
518
else
4504)
else
(if i.val < 2327 then
2953
else
4505)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
4694
else
3888)
else
(if i.val < 2331 then
1448
else
1340))
else
(if i.val < 2334 then
(if i.val < 2333 then
1135
else
1285)
else
(if i.val < 2335 then
5182
else
6666)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
1324
else
5058)
else
(if i.val < 2339 then
5875
else
6667))
else
(if i.val < 2342 then
(if i.val < 2341 then
6668
else
6669)
else
(if i.val < 2343 then
5502
else
5174)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
6670
else
5878)
else
(if i.val < 2347 then
3111
else
6585))
else
(if i.val < 2350 then
(if i.val < 2349 then
6586
else
1232)
else
(if i.val < 2351 then
5208
else
4551))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
564
else
2819)
else
(if i.val < 2355 then
6566
else
5820))
else
(if i.val < 2358 then
(if i.val < 2357 then
3054
else
6671)
else
(if i.val < 2359 then
1158
else
3422)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
1879
else
4763)
else
(if i.val < 2363 then
6672
else
6536))
else
(if i.val < 2366 then
(if i.val < 2365 then
6673
else
5972)
else
(if i.val < 2367 then
3325
else
5205))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
6674
else
3051)
else
(if i.val < 2371 then
3844
else
6675))
else
(if i.val < 2374 then
(if i.val < 2373 then
2558
else
6676)
else
(if i.val < 2375 then
5372
else
6677)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
6678
else
6679)
else
(if i.val < 2379 then
4705
else
2505))
else
(if i.val < 2382 then
(if i.val < 2381 then
2771
else
4424)
else
(if i.val < 2383 then
4704
else
4609))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
6485
else
6523)
else
(if i.val < 2387 then
6587
else
1539))
else
(if i.val < 2390 then
(if i.val < 2389 then
6571
else
6593)
else
(if i.val < 2391 then
6594
else
5373)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
4608
else
4610)
else
(if i.val < 2395 then
6680
else
6603))
else
(if i.val < 2398 then
(if i.val < 2397 then
4013
else
6681)
else
(if i.val < 2399 then
4700
else
2578)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
2572
else
6509)
else
(if i.val < 2403 then
6349
else
6549))
else
(if i.val < 2406 then
(if i.val < 2405 then
4628
else
6135)
else
(if i.val < 2407 then
6682
else
6683)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
4703
else
2212)
else
(if i.val < 2411 then
4636
else
4637))
else
(if i.val < 2414 then
(if i.val < 2413 then
622
else
4646)
else
(if i.val < 2415 then
4647
else
4644))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
4648
else
2330)
else
(if i.val < 2419 then
625
else
623))
else
(if i.val < 2422 then
(if i.val < 2421 then
624
else
2542)
else
(if i.val < 2423 then
5409
else
4493)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
2800
else
5414)
else
(if i.val < 2427 then
5417
else
2815))
else
(if i.val < 2430 then
(if i.val < 2429 then
5413
else
2750)
else
(if i.val < 2431 then
5432
else
4906)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
5433
else
5434)
else
(if i.val < 2435 then
5430
else
5047))
else
(if i.val < 2438 then
(if i.val < 2437 then
5435
else
5436)
else
(if i.val < 2439 then
5437
else
5438)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
3847
else
2312)
else
(if i.val < 2443 then
5429
else
4672))
else
(if i.val < 2446 then
(if i.val < 2445 then
4792
else
5924)
else
(if i.val < 2447 then
5138
else
6684))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
6240
else
6685)
else
(if i.val < 2451 then
6446
else
2814))
else
(if i.val < 2454 then
(if i.val < 2453 then
6686
else
6687)
else
(if i.val < 2455 then
6688
else
6689)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
6690
else
6402)
else
(if i.val < 2459 then
477
else
478))
else
(if i.val < 2462 then
(if i.val < 2461 then
461
else
2548)
else
(if i.val < 2463 then
2499
else
2513)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
4690
else
2576)
else
(if i.val < 2467 then
4691
else
4692))
else
(if i.val < 2470 then
(if i.val < 2469 then
3049
else
4693)
else
(if i.val < 2471 then
4698
else
2547)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
2613
else
4699)
else
(if i.val < 2475 then
4701
else
4702))
else
(if i.val < 2478 then
(if i.val < 2477 then
6027
else
2764)
else
(if i.val < 2479 then
4715
else
6028))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
6029
else
3942)
else
(if i.val < 2483 then
5928
else
6030))
else
(if i.val < 2486 then
(if i.val < 2485 then
5444
else
4388)
else
(if i.val < 2487 then
5927
else
1923)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
4880
else
2325)
else
(if i.val < 2491 then
2697
else
4472))
else
(if i.val < 2494 then
(if i.val < 2493 then
6031
else
6032)
else
(if i.val < 2495 then
6033
else
6034))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
1047
else
5931)
else
(if i.val < 2499 then
3535
else
1046))
else
(if i.val < 2502 then
(if i.val < 2501 then
6035
else
5859)
else
(if i.val < 2503 then
6036
else
1088)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
4760
else
4761)
else
(if i.val < 2507 then
4762
else
5929))
else
(if i.val < 2510 then
(if i.val < 2509 then
5930
else
4879)
else
(if i.val < 2511 then
5857
else
5858))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
6252
else
1033)
else
(if i.val < 2515 then
6253
else
5597))
else
(if i.val < 2518 then
(if i.val < 2517 then
6254
else
6255)
else
(if i.val < 2519 then
6256
else
6257)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
5287
else
6258)
else
(if i.val < 2523 then
4507
else
2323))
else
(if i.val < 2526 then
(if i.val < 2525 then
5792
else
5440)
else
(if i.val < 2527 then
3906
else
6259)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
5418
else
5596)
else
(if i.val < 2531 then
3534
else
3536))
else
(if i.val < 2534 then
(if i.val < 2533 then
812
else
6260)
else
(if i.val < 2535 then
4515
else
6261)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
1615
else
2765)
else
(if i.val < 2539 then
5793
else
5795))
else
(if i.val < 2542 then
(if i.val < 2541 then
3795
else
574)
else
(if i.val < 2543 then
1217
else
6262))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
6263
else
1235)
else
(if i.val < 2547 then
5794
else
1186))
else
(if i.val < 2550 then
(if i.val < 2549 then
1015
else
4973)
else
(if i.val < 2551 then
5651
else
6264)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
5351
else
2932)
else
(if i.val < 2555 then
5650
else
4344))
else
(if i.val < 2558 then
(if i.val < 2557 then
4345
else
4346)
else
(if i.val < 2559 then
4308
else
495)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0005 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
4835
else
4836)
else
(if i.val < 2563 then
4837
else
4838))
else
(if i.val < 2566 then
(if i.val < 2565 then
4839
else
2855)
else
(if i.val < 2567 then
4840
else
4841)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
4842
else
2673)
else
(if i.val < 2571 then
5791
else
3558))
else
(if i.val < 2574 then
(if i.val < 2573 then
4376
else
1261)
else
(if i.val < 2575 then
5590
else
5591))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
1121
else
4863)
else
(if i.val < 2579 then
5648
else
5649))
else
(if i.val < 2582 then
(if i.val < 2581 then
511
else
2627)
else
(if i.val < 2583 then
3632
else
2633)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
2650
else
6020)
else
(if i.val < 2587 then
6691
else
6692))
else
(if i.val < 2590 then
(if i.val < 2589 then
2555
else
1175)
else
(if i.val < 2591 then
1231
else
6693)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
4953
else
1194)
else
(if i.val < 2595 then
1173
else
6694))
else
(if i.val < 2598 then
(if i.val < 2597 then
6695
else
1172)
else
(if i.val < 2599 then
1187
else
1183)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
5939
else
4707)
else
(if i.val < 2603 then
5312
else
4649))
else
(if i.val < 2606 then
(if i.val < 2605 then
1072
else
5443)
else
(if i.val < 2607 then
1253
else
5441))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
5925
else
6696)
else
(if i.val < 2611 then
6697
else
1760))
else
(if i.val < 2614 then
(if i.val < 2613 then
6698
else
4437)
else
(if i.val < 2615 then
4710
else
2598)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
1174
else
1748)
else
(if i.val < 2619 then
1176
else
1182))
else
(if i.val < 2622 then
(if i.val < 2621 then
4933
else
1112)
else
(if i.val < 2623 then
4924
else
506))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
4936
else
4392)
else
(if i.val < 2627 then
1431
else
4923))
else
(if i.val < 2630 then
(if i.val < 2629 then
4941
else
6163)
else
(if i.val < 2631 then
5108
else
4949)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
4950
else
4942)
else
(if i.val < 2635 then
2630
else
6560))
else
(if i.val < 2638 then
(if i.val < 2637 then
5452
else
4384)
else
(if i.val < 2639 then
6699
else
5450))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
2244
else
2618)
else
(if i.val < 2643 then
5451
else
1581))
else
(if i.val < 2646 then
(if i.val < 2645 then
999
else
4391)
else
(if i.val < 2647 then
3079
else
701)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
3350
else
2586)
else
(if i.val < 2651 then
6700
else
6323))
else
(if i.val < 2654 then
(if i.val < 2653 then
4651
else
4978)
else
(if i.val < 2655 then
4979
else
4980)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
2247
else
4987)
else
(if i.val < 2659 then
1502
else
1516))
else
(if i.val < 2662 then
(if i.val < 2661 then
5439
else
4405)
else
(if i.val < 2663 then
1004
else
4469)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
4383
else
5445)
else
(if i.val < 2667 then
5446
else
5447))
else
(if i.val < 2670 then
(if i.val < 2669 then
5448
else
4397)
else
(if i.val < 2671 then
5449
else
1599))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
1142
else
1618)
else
(if i.val < 2675 then
1632
else
1570))
else
(if i.val < 2678 then
(if i.val < 2677 then
1645
else
4650)
else
(if i.val < 2679 then
3318
else
5585)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
6701
else
6702)
else
(if i.val < 2683 then
3145
else
1759))
else
(if i.val < 2686 then
(if i.val < 2685 then
3792
else
6703)
else
(if i.val < 2687 then
6704
else
6705)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
6706
else
4511)
else
(if i.val < 2691 then
6567
else
1636))
else
(if i.val < 2694 then
(if i.val < 2693 then
3226
else
3907)
else
(if i.val < 2695 then
6707
else
3442)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
5460
else
6386)
else
(if i.val < 2699 then
1109
else
6708))
else
(if i.val < 2702 then
(if i.val < 2701 then
6709
else
6710)
else
(if i.val < 2703 then
6711
else
1509))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
1473
else
6712)
else
(if i.val < 2707 then
1008
else
2303))
else
(if i.val < 2710 then
(if i.val < 2709 then
6138
else
6713)
else
(if i.val < 2711 then
6714
else
6337)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
4536
else
5322)
else
(if i.val < 2715 then
3800
else
3797))
else
(if i.val < 2718 then
(if i.val < 2717 then
3802
else
5609)
else
(if i.val < 2719 then
6715
else
6716)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
5608
else
6347)
else
(if i.val < 2723 then
3180
else
2252))
else
(if i.val < 2726 then
(if i.val < 2725 then
6075
else
6717)
else
(if i.val < 2727 then
5227
else
6352)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
3796
else
1724)
else
(if i.val < 2731 then
5468
else
5469))
else
(if i.val < 2734 then
(if i.val < 2733 then
6718
else
1690)
else
(if i.val < 2735 then
5463
else
5461))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
4657
else
1123)
else
(if i.val < 2739 then
4658
else
5464))
else
(if i.val < 2742 then
(if i.val < 2741 then
6719
else
5466)
else
(if i.val < 2743 then
4959
else
5100)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
5465
else
4659)
else
(if i.val < 2747 then
1579
else
5454))
else
(if i.val < 2750 then
(if i.val < 2749 then
3918
else
5459)
else
(if i.val < 2751 then
1259
else
4653))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
4654
else
4660)
else
(if i.val < 2755 then
6720
else
6721))
else
(if i.val < 2758 then
(if i.val < 2757 then
6510
else
4656)
else
(if i.val < 2759 then
5189
else
6722)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
2851
else
513)
else
(if i.val < 2763 then
4988
else
4989))
else
(if i.val < 2766 then
(if i.val < 2765 then
4990
else
1654)
else
(if i.val < 2767 then
4991
else
4992))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
1567
else
4993)
else
(if i.val < 2771 then
4907
else
4908))
else
(if i.val < 2774 then
(if i.val < 2773 then
541
else
542)
else
(if i.val < 2775 then
543
else
1529)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
1474
else
650)
else
(if i.val < 2779 then
5141
else
5142))
else
(if i.val < 2782 then
(if i.val < 2781 then
1468
else
3139)
else
(if i.val < 2783 then
5143
else
5144)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
5145
else
1022)
else
(if i.val < 2787 then
5147
else
5148))
else
(if i.val < 2790 then
(if i.val < 2789 then
5149
else
5150)
else
(if i.val < 2791 then
5151
else
5453)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
5455
else
5456)
else
(if i.val < 2795 then
5458
else
2823))
else
(if i.val < 2798 then
(if i.val < 2797 then
5462
else
1220)
else
(if i.val < 2799 then
4411
else
4412))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
1288
else
4486)
else
(if i.val < 2803 then
4487
else
4488))
else
(if i.val < 2806 then
(if i.val < 2805 then
4489
else
4490)
else
(if i.val < 2807 then
4491
else
4492)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
2745
else
549)
else
(if i.val < 2811 then
4652
else
3205))
else
(if i.val < 2814 then
(if i.val < 2813 then
4655
else
6611)
else
(if i.val < 2815 then
1612
else
1264))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
5195
else
552)
else
(if i.val < 2819 then
5020
else
1723))
else
(if i.val < 2822 then
(if i.val < 2821 then
5207
else
1727)
else
(if i.val < 2823 then
5622
else
3586)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
6723
else
6724)
else
(if i.val < 2827 then
6725
else
6726))
else
(if i.val < 2830 then
(if i.val < 2829 then
4711
else
6727)
else
(if i.val < 2831 then
6728
else
6729))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
6730
else
5601)
else
(if i.val < 2835 then
6731
else
6732))
else
(if i.val < 2838 then
(if i.val < 2837 then
6733
else
6734)
else
(if i.val < 2839 then
6735
else
6736)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
6737
else
6738)
else
(if i.val < 2843 then
2736
else
5481))
else
(if i.val < 2846 then
(if i.val < 2845 then
6739
else
3065)
else
(if i.val < 2847 then
5038
else
5121)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
5231
else
4521)
else
(if i.val < 2851 then
4520
else
5480))
else
(if i.val < 2854 then
(if i.val < 2853 then
5478
else
6740)
else
(if i.val < 2855 then
3349
else
1585)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
5074
else
3418)
else
(if i.val < 2859 then
5022
else
1357))
else
(if i.val < 2862 then
(if i.val < 2861 then
5016
else
5284)
else
(if i.val < 2863 then
4572
else
4495))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
2346
else
834)
else
(if i.val < 2867 then
4508
else
4661))
else
(if i.val < 2870 then
(if i.val < 2869 then
6284
else
4395)
else
(if i.val < 2871 then
6741
else
6272)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
6742
else
4687)
else
(if i.val < 2875 then
6743
else
4667))
else
(if i.val < 2878 then
(if i.val < 2877 then
6744
else
3242)
else
(if i.val < 2879 then
5882
else
6745))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
6746
else
6747)
else
(if i.val < 2883 then
1702
else
5042))
else
(if i.val < 2886 then
(if i.val < 2885 then
5272
else
6748)
else
(if i.val < 2887 then
5758
else
5485)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
5092
else
6749)
else
(if i.val < 2891 then
4764
else
5298))
else
(if i.val < 2894 then
(if i.val < 2893 then
1630
else
6590)
else
(if i.val < 2895 then
5483
else
5484))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
5203
else
6197)
else
(if i.val < 2899 then
6750
else
5999))
else
(if i.val < 2902 then
(if i.val < 2901 then
5494
else
2235)
else
(if i.val < 2903 then
4513
else
6538)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
4456
else
5200)
else
(if i.val < 2907 then
6751
else
5482))
else
(if i.val < 2910 then
(if i.val < 2909 then
591
else
5497)
else
(if i.val < 2911 then
5255
else
5318)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
3050
else
5470)
else
(if i.val < 2915 then
5479
else
5498))
else
(if i.val < 2918 then
(if i.val < 2917 then
4671
else
4670)
else
(if i.val < 2919 then
3060
else
6642)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
4669
else
5427)
else
(if i.val < 2923 then
4937
else
5490))
else
(if i.val < 2926 then
(if i.val < 2925 then
1493
else
4955)
else
(if i.val < 2927 then
2783
else
4310))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
5314
else
1862)
else
(if i.val < 2931 then
6524
else
5292))
else
(if i.val < 2934 then
(if i.val < 2933 then
5273
else
6582)
else
(if i.val < 2935 then
6580
else
4571)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
5354
else
6583)
else
(if i.val < 2939 then
6584
else
2652))
else
(if i.val < 2942 then
(if i.val < 2941 then
5033
else
5364)
else
(if i.val < 2943 then
5361
else
5363)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
5307
else
5365)
else
(if i.val < 2947 then
5366
else
587))
else
(if i.val < 2950 then
(if i.val < 2949 then
1687
else
1577)
else
(if i.val < 2951 then
459
else
583)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
588
else
1237)
else
(if i.val < 2955 then
4309
else
2907))
else
(if i.val < 2958 then
(if i.val < 2957 then
590
else
5477)
else
(if i.val < 2959 then
4662
else
1575))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
3154
else
4597)
else
(if i.val < 2963 then
1483
else
2443))
else
(if i.val < 2966 then
(if i.val < 2965 then
1482
else
6508)
else
(if i.val < 2967 then
4590
else
6403)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
6752
else
6356)
else
(if i.val < 2971 then
6753
else
6321))
else
(if i.val < 2974 then
(if i.val < 2973 then
6754
else
6755)
else
(if i.val < 2975 then
4668
else
1578)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
3921
else
6756)
else
(if i.val < 2979 then
6424
else
4666))
else
(if i.val < 2982 then
(if i.val < 2981 then
514
else
515)
else
(if i.val < 2983 then
510
else
545)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
546
else
535)
else
(if i.val < 2987 then
529
else
550))
else
(if i.val < 2990 then
(if i.val < 2989 then
551
else
613)
else
(if i.val < 2991 then
614
else
615))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
616
else
565)
else
(if i.val < 2995 then
579
else
617))
else
(if i.val < 2998 then
(if i.val < 2997 then
618
else
619)
else
(if i.val < 2999 then
620
else
593)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
582
else
592)
else
(if i.val < 3003 then
580
else
626))
else
(if i.val < 3006 then
(if i.val < 3005 then
627
else
628)
else
(if i.val < 3007 then
5127
else
5128))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
5129
else
2599)
else
(if i.val < 3011 then
5403
else
5404))
else
(if i.val < 3014 then
(if i.val < 3013 then
5406
else
5407)
else
(if i.val < 3015 then
5408
else
5410)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
736
else
3870)
else
(if i.val < 3019 then
1686
else
2349))
else
(if i.val < 3022 then
(if i.val < 3021 then
3155
else
5411)
else
(if i.val < 3023 then
3238
else
5412))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
1504
else
3210)
else
(if i.val < 3027 then
774
else
5415))
else
(if i.val < 3030 then
(if i.val < 3029 then
5378
else
5337)
else
(if i.val < 3031 then
5419
else
5306)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
5420
else
5421)
else
(if i.val < 3035 then
5422
else
1425))
else
(if i.val < 3038 then
(if i.val < 3037 then
4847
else
5423)
else
(if i.val < 3039 then
5424
else
2626)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
5329
else
5425)
else
(if i.val < 3043 then
5426
else
3457))
else
(if i.val < 3046 then
(if i.val < 3045 then
5428
else
2197)
else
(if i.val < 3047 then
2195
else
5341)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
5431
else
1091)
else
(if i.val < 3051 then
4516
else
3248))
else
(if i.val < 3054 then
(if i.val < 3053 then
4799
else
5471)
else
(if i.val < 3055 then
5472
else
5473))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
5474
else
5475)
else
(if i.val < 3059 then
2941
else
5476))
else
(if i.val < 3062 then
(if i.val < 3061 then
5486
else
5487)
else
(if i.val < 3063 then
5291
else
5488)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
2922
else
5055)
else
(if i.val < 3067 then
5489
else
4824))
else
(if i.val < 3070 then
(if i.val < 3069 then
5491
else
5492)
else
(if i.val < 3071 then
5493
else
5247)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0006 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
5331
else
5495)
else
(if i.val < 3075 then
5496
else
471))
else
(if i.val < 3078 then
(if i.val < 3077 then
460
else
473)
else
(if i.val < 3079 then
455
else
4480)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
4632
else
492)
else
(if i.val < 3083 then
4633
else
2526))
else
(if i.val < 3086 then
(if i.val < 3085 then
4634
else
2534)
else
(if i.val < 3087 then
2551
else
4635))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
4638
else
4639)
else
(if i.val < 3091 then
4581
else
4612))
else
(if i.val < 3094 then
(if i.val < 3093 then
1708
else
4640)
else
(if i.val < 3095 then
4641
else
4642)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
4643
else
4645)
else
(if i.val < 3099 then
808
else
4323))
else
(if i.val < 3102 then
(if i.val < 3101 then
3542
else
2375)
else
(if i.val < 3103 then
4663
else
4664)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
4665
else
3119)
else
(if i.val < 3107 then
479
else
5570))
else
(if i.val < 3110 then
(if i.val < 3109 then
6220
else
6221)
else
(if i.val < 3111 then
1463
else
2864)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
6222
else
4721)
else
(if i.val < 3115 then
6223
else
6224))
else
(if i.val < 3118 then
(if i.val < 3117 then
6225
else
6226)
else
(if i.val < 3119 then
3662
else
6227))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
6228
else
3793)
else
(if i.val < 3123 then
5664
else
6229))
else
(if i.val < 3126 then
(if i.val < 3125 then
6230
else
4864)
else
(if i.val < 3127 then
828
else
2892)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
3860
else
5222)
else
(if i.val < 3131 then
3528
else
5595))
else
(if i.val < 3134 then
(if i.val < 3133 then
2739
else
6231)
else
(if i.val < 3135 then
2747
else
6232))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
2748
else
6233)
else
(if i.val < 3139 then
6234
else
1042))
else
(if i.val < 3142 then
(if i.val < 3141 then
4498
else
5264)
else
(if i.val < 3143 then
5936
else
3881)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
2789
else
4463)
else
(if i.val < 3147 then
2367
else
2364))
else
(if i.val < 3150 then
(if i.val < 3149 then
2787
else
1043)
else
(if i.val < 3151 then
6235
else
5508))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
6236
else
6237)
else
(if i.val < 3155 then
5360
else
1246))
else
(if i.val < 3158 then
(if i.val < 3157 then
2769
else
6189)
else
(if i.val < 3159 then
6193
else
5196)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
5751
else
6238)
else
(if i.val < 3163 then
5667
else
5668))
else
(if i.val < 3166 then
(if i.val < 3165 then
6173
else
6239)
else
(if i.val < 3167 then
4886
else
5646)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
5647
else
676)
else
(if i.val < 3171 then
4616
else
5776))
else
(if i.val < 3174 then
(if i.val < 3173 then
5774
else
5783)
else
(if i.val < 3175 then
2768
else
5784)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
3188
else
5781)
else
(if i.val < 3179 then
6241
else
6242))
else
(if i.val < 3182 then
(if i.val < 3181 then
6243
else
644)
else
(if i.val < 3183 then
5661
else
5662))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
5663
else
5665)
else
(if i.val < 3187 then
5666
else
3967))
else
(if i.val < 3190 then
(if i.val < 3189 then
1540
else
2790)
else
(if i.val < 3191 then
1032
else
5091)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
5891
else
6265)
else
(if i.val < 3195 then
6266
else
4582))
else
(if i.val < 3198 then
(if i.val < 3197 then
6267
else
6268)
else
(if i.val < 3199 then
2844
else
2839)))))))
else
(if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
6269
else
6270)
else
(if i.val < 3203 then
2299
else
5697))
else
(if i.val < 3206 then
(if i.val < 3205 then
4862
else
6271)
else
(if i.val < 3207 then
1052
else
5152)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
2889
else
1227)
else
(if i.val < 3211 then
1254
else
6273))
else
(if i.val < 3214 then
(if i.val < 3213 then
6274
else
5153)
else
(if i.val < 3215 then
1044
else
6143))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
3864
else
2767)
else
(if i.val < 3219 then
2796
else
5913))
else
(if i.val < 3222 then
(if i.val < 3221 then
4497
else
2311)
else
(if i.val < 3223 then
1919
else
1064)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
6103
else
837)
else
(if i.val < 3227 then
6275
else
3294))
else
(if i.val < 3230 then
(if i.val < 3229 then
2867
else
2786)
else
(if i.val < 3231 then
4902
else
5804)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
5805
else
1013)
else
(if i.val < 3235 then
5799
else
5338))
else
(if i.val < 3238 then
(if i.val < 3237 then
5806
else
5345)
else
(if i.val < 3239 then
1281
else
5656)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
5727
else
2970)
else
(if i.val < 3243 then
5749
else
6129))
else
(if i.val < 3246 then
(if i.val < 3245 then
6181
else
1952)
else
(if i.val < 3247 then
5748
else
5750))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
2369
else
4414)
else
(if i.val < 3251 then
1010
else
5753))
else
(if i.val < 3254 then
(if i.val < 3253 then
1847
else
4428)
else
(if i.val < 3255 then
1262
else
6276)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
5655
else
1110)
else
(if i.val < 3259 then
2968
else
6277))
else
(if i.val < 3262 then
(if i.val < 3261 then
419
else
496)
else
(if i.val < 3263 then
497
else
498))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
671
else
672)
else
(if i.val < 3267 then
662
else
673))
else
(if i.val < 3270 then
(if i.val < 3269 then
674
else
663)
else
(if i.val < 3271 then
657
else
677)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
678
else
4828)
else
(if i.val < 3275 then
5769
else
5770))
else
(if i.val < 3278 then
(if i.val < 3277 then
5771
else
690)
else
(if i.val < 3279 then
5772
else
5773))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
3358
else
5775)
else
(if i.val < 3283 then
5777
else
5164))
else
(if i.val < 3286 then
(if i.val < 3285 then
2260
else
5778)
else
(if i.val < 3287 then
4401
else
5755)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
5779
else
5780)
else
(if i.val < 3291 then
1014
else
3850))
else
(if i.val < 3294 then
(if i.val < 3293 then
2188
else
5782)
else
(if i.val < 3295 then
5598
else
4742)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
3234
else
5797)
else
(if i.val < 3299 then
5798
else
2827))
else
(if i.val < 3302 then
(if i.val < 3301 then
3848
else
5801)
else
(if i.val < 3303 then
3872
else
5802)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
5735
else
5803)
else
(if i.val < 3307 then
642
else
643))
else
(if i.val < 3310 then
(if i.val < 3309 then
2681
else
1248)
else
(if i.val < 3311 then
2493
else
2446))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
5645
else
3587)
else
(if i.val < 3315 then
1085
else
5652))
else
(if i.val < 3318 then
(if i.val < 3317 then
5653
else
5654)
else
(if i.val < 3319 then
4965
else
4850)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
6021
else
4809)
else
(if i.val < 3323 then
4852
else
2564))
else
(if i.val < 3326 then
(if i.val < 3325 then
1735
else
1912)
else
(if i.val < 3327 then
1466
else
6022))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
1465
else
6004)
else
(if i.val < 3331 then
5500
else
6023))
else
(if i.val < 3334 then
(if i.val < 3333 then
5864
else
6024)
else
(if i.val < 3335 then
5856
else
5919)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
5926
else
6025)
else
(if i.val < 3339 then
3399
else
2746))
else
(if i.val < 3342 then
(if i.val < 3341 then
5862
else
5863)
else
(if i.val < 3343 then
4843
else
1462))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
569
else
6037)
else
(if i.val < 3347 then
2556
else
5080))
else
(if i.val < 3350 then
(if i.val < 3349 then
6038
else
5995)
else
(if i.val < 3351 then
4845
else
3124)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
1155
else
6039)
else
(if i.val < 3355 then
6040
else
3565))
else
(if i.val < 3358 then
(if i.val < 3357 then
2557
else
4846)
else
(if i.val < 3359 then
1167
else
2862)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
1908
else
1181)
else
(if i.val < 3363 then
5937
else
3605))
else
(if i.val < 3366 then
(if i.val < 3365 then
4915
else
5899)
else
(if i.val < 3367 then
4831
else
2563)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
5909
else
2389)
else
(if i.val < 3371 then
1003
else
4910))
else
(if i.val < 3374 then
(if i.val < 3373 then
2603
else
6041)
else
(if i.val < 3375 then
6042
else
4681))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
693
else
694)
else
(if i.val < 3379 then
689
else
695))
else
(if i.val < 3382 then
(if i.val < 3381 then
5918
else
2332)
else
(if i.val < 3383 then
1075
else
5920)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
5921
else
5922)
else
(if i.val < 3387 then
5923
else
4439))
else
(if i.val < 3390 then
(if i.val < 3389 then
5932
else
5934)
else
(if i.val < 3391 then
5252
else
3555))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
5935
else
1157)
else
(if i.val < 3395 then
2376
else
5855))
else
(if i.val < 3398 then
(if i.val < 3397 then
1491
else
5860)
else
(if i.val < 3399 then
4393
else
5401)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
2549
else
4819)
else
(if i.val < 3403 then
6003
else
5119))
else
(if i.val < 3406 then
(if i.val < 3405 then
6043
else
6044)
else
(if i.val < 3407 then
6045
else
1694))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
1867
else
1501)
else
(if i.val < 3411 then
4853
else
1332))
else
(if i.val < 3414 then
(if i.val < 3413 then
6046
else
6007)
else
(if i.val < 3415 then
6002
else
1065)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
5967
else
1469)
else
(if i.val < 3419 then
2281
else
1892))
else
(if i.val < 3422 then
(if i.val < 3421 then
702
else
5966)
else
(if i.val < 3423 then
5965
else
3120)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
4805
else
5987)
else
(if i.val < 3427 then
5356
else
6047))
else
(if i.val < 3430 then
(if i.val < 3429 then
5614
else
6048)
else
(if i.val < 3431 then
3573
else
3224)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
2860
else
3579)
else
(if i.val < 3435 then
5030
else
3891))
else
(if i.val < 3438 then
(if i.val < 3437 then
2940
else
6049)
else
(if i.val < 3439 then
1736
else
5989))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
6010
else
5358)
else
(if i.val < 3443 then
6050
else
6051))
else
(if i.val < 3446 then
(if i.val < 3445 then
6006
else
6009)
else
(if i.val < 3447 then
6008
else
5992)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
716
else
3890)
else
(if i.val < 3451 then
586
else
3926))
else
(if i.val < 3454 then
(if i.val < 3453 then
709
else
710)
else
(if i.val < 3455 then
5015
else
2852)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
5996
else
1353)
else
(if i.val < 3459 then
2266
else
2676))
else
(if i.val < 3462 then
(if i.val < 3461 then
6005
else
711)
else
(if i.val < 3463 then
688
else
4407)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
4972
else
3838)
else
(if i.val < 3467 then
703
else
715))
else
(if i.val < 3470 then
(if i.val < 3469 then
4810
else
5281)
else
(if i.val < 3471 then
707
else
4056))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
706
else
2644)
else
(if i.val < 3475 then
2597
else
2594))
else
(if i.val < 3478 then
(if i.val < 3477 then
1932
else
2675)
else
(if i.val < 3479 then
6052
else
6053)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
2959
else
6054)
else
(if i.val < 3483 then
2949
else
2975))
else
(if i.val < 3486 then
(if i.val < 3485 then
6055
else
2737)
else
(if i.val < 3487 then
879
else
5569)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
6056
else
6057)
else
(if i.val < 3491 then
6058
else
6059))
else
(if i.val < 3494 then
(if i.val < 3493 then
6060
else
5825)
else
(if i.val < 3495 then
6061
else
2643)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
2267
else
3832)
else
(if i.val < 3499 then
6062
else
6063))
else
(if i.val < 3502 then
(if i.val < 3501 then
6064
else
4434)
else
(if i.val < 3503 then
6016
else
6065))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
5017
else
2536)
else
(if i.val < 3507 then
3859
else
3836))
else
(if i.val < 3510 then
(if i.val < 3509 then
3556
else
2674)
else
(if i.val < 3511 then
3551
else
5137)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
2691
else
6015)
else
(if i.val < 3515 then
679
else
680))
else
(if i.val < 3518 then
(if i.val < 3517 then
681
else
481)
else
(if i.val < 3519 then
482
else
483))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
683
else
684)
else
(if i.val < 3523 then
685
else
686))
else
(if i.val < 3526 then
(if i.val < 3525 then
696
else
697)
else
(if i.val < 3527 then
705
else
5914)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
5887
else
6278)
else
(if i.val < 3531 then
4517
else
6279))
else
(if i.val < 3534 then
(if i.val < 3533 then
5543
else
6194)
else
(if i.val < 3535 then
6120
else
6280))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
5014
else
5512)
else
(if i.val < 3539 then
2296
else
4512))
else
(if i.val < 3542 then
(if i.val < 3541 then
3874
else
6281)
else
(if i.val < 3543 then
6282
else
5964)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
6283
else
5158)
else
(if i.val < 3547 then
5157
else
1299))
else
(if i.val < 3550 then
(if i.val < 3549 then
1051
else
3543)
else
(if i.val < 3551 then
1873
else
1633)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
6121
else
1050)
else
(if i.val < 3555 then
1878
else
1871))
else
(if i.val < 3558 then
(if i.val < 3557 then
1629
else
1882)
else
(if i.val < 3559 then
1593
else
1631)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
5893
else
6105)
else
(if i.val < 3563 then
6106
else
567))
else
(if i.val < 3566 then
(if i.val < 3565 then
5564
else
4423)
else
(if i.val < 3567 then
1894
else
4874))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
6112
else
6176)
else
(if i.val < 3571 then
5615
else
4716))
else
(if i.val < 3574 then
(if i.val < 3573 then
5530
else
6067)
else
(if i.val < 3575 then
3092
else
743)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
745
else
739)
else
(if i.val < 3579 then
6095
else
6094))
else
(if i.val < 3582 then
(if i.val < 3581 then
2973
else
6150)
else
(if i.val < 3583 then
6144
else
753)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0007 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
6145
else
5304)
else
(if i.val < 3587 then
2795
else
6285))
else
(if i.val < 3590 then
(if i.val < 3589 then
5162
else
4553)
else
(if i.val < 3591 then
2201
else
6286)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
3869
else
2702)
else
(if i.val < 3595 then
2350
else
3883))
else
(if i.val < 3598 then
(if i.val < 3597 then
6287
else
3582)
else
(if i.val < 3599 then
6195
else
456))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
1941
else
6288)
else
(if i.val < 3603 then
1942
else
1341))
else
(if i.val < 3606 then
(if i.val < 3605 then
3908
else
5012)
else
(if i.val < 3607 then
2322
else
5085)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
1944
else
6153)
else
(if i.val < 3611 then
6289
else
5069))
else
(if i.val < 3614 then
(if i.val < 3613 then
6290
else
6291)
else
(if i.val < 3615 then
6165
else
4044)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
6164
else
776)
else
(if i.val < 3619 then
2617
else
5086))
else
(if i.val < 3622 then
(if i.val < 3621 then
760
else
6166)
else
(if i.val < 3623 then
3438
else
6167)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
754
else
6171)
else
(if i.val < 3627 then
4722
else
6168))
else
(if i.val < 3630 then
(if i.val < 3629 then
4292
else
1931)
else
(if i.val < 3631 then
6172
else
763))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
4891
else
5251)
else
(if i.val < 3635 then
2683
else
4445))
else
(if i.val < 3638 then
(if i.val < 3637 then
6188
else
6179)
else
(if i.val < 3639 then
2611
else
6177)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
4782
else
6180)
else
(if i.val < 3643 then
6182
else
6190))
else
(if i.val < 3646 then
(if i.val < 3645 then
6191
else
6184)
else
(if i.val < 3647 then
872
else
6192))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
742
else
764)
else
(if i.val < 3651 then
660
else
659))
else
(if i.val < 3654 then
(if i.val < 3653 then
2964
else
2733)
else
(if i.val < 3655 then
2882
else
6123)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
741
else
731)
else
(if i.val < 3659 then
738
else
740))
else
(if i.val < 3662 then
(if i.val < 3661 then
746
else
773)
else
(if i.val < 3663 then
6155
else
903))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
755
else
4058)
else
(if i.val < 3667 then
4459
else
5082))
else
(if i.val < 3670 then
(if i.val < 3669 then
528
else
1858)
else
(if i.val < 3671 then
6161
else
756)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
656
else
6162)
else
(if i.val < 3675 then
4054
else
5102))
else
(if i.val < 3678 then
(if i.val < 3677 then
751
else
6292)
else
(if i.val < 3679 then
6293
else
6294)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
2187
else
6295)
else
(if i.val < 3683 then
6296
else
6297))
else
(if i.val < 3686 then
(if i.val < 3685 then
3343
else
3110)
else
(if i.val < 3687 then
3328
else
3326)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
6298
else
2704)
else
(if i.val < 3691 then
6299
else
5823))
else
(if i.val < 3694 then
(if i.val < 3693 then
5985
else
2962)
else
(if i.val < 3695 then
6300
else
3396))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
5822
else
2278)
else
(if i.val < 3699 then
6301
else
2191))
else
(if i.val < 3702 then
(if i.val < 3701 then
6302
else
4552)
else
(if i.val < 3703 then
4447
else
2280)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
429
else
6303)
else
(if i.val < 3707 then
6304
else
6305))
else
(if i.val < 3710 then
(if i.val < 3709 then
2672
else
5173)
else
(if i.val < 3711 then
1443
else
6306)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
6307
else
4673)
else
(if i.val < 3715 then
6014
else
6308))
else
(if i.val < 3718 then
(if i.val < 3717 then
6309
else
3393)
else
(if i.val < 3719 then
2358
else
6310)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
3409
else
6311)
else
(if i.val < 3723 then
6312
else
6313))
else
(if i.val < 3726 then
(if i.val < 3725 then
554
else
6314)
else
(if i.val < 3727 then
4750
else
6209))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
6315
else
2387)
else
(if i.val < 3731 then
2948
else
4745))
else
(if i.val < 3734 then
(if i.val < 3733 then
6316
else
6317)
else
(if i.val < 3735 then
3407
else
6318)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
6319
else
6320)
else
(if i.val < 3739 then
2729
else
6131))
else
(if i.val < 3742 then
(if i.val < 3741 then
3837
else
6207)
else
(if i.val < 3743 then
3324
else
6208)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
6199
else
421)
else
(if i.val < 3747 then
629
else
630))
else
(if i.val < 3750 then
(if i.val < 3749 then
631
else
633)
else
(if i.val < 3751 then
634
else
635)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
636
else
637)
else
(if i.val < 3755 then
640
else
414))
else
(if i.val < 3758 then
(if i.val < 3757 then
415
else
485)
else
(if i.val < 3759 then
486
else
487))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
488
else
489)
else
(if i.val < 3763 then
490
else
645))
else
(if i.val < 3766 then
(if i.val < 3765 then
646
else
647)
else
(if i.val < 3767 then
648
else
651)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
653
else
654)
else
(if i.val < 3771 then
655
else
664))
else
(if i.val < 3774 then
(if i.val < 3773 then
665
else
730)
else
(if i.val < 3775 then
733
else
734))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
737
else
6201)
else
(if i.val < 3779 then
5761
else
5765))
else
(if i.val < 3782 then
(if i.val < 3781 then
6757
else
1725)
else
(if i.val < 3783 then
6758
else
6136)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
6759
else
2392)
else
(if i.val < 3787 then
6333
else
2693))
else
(if i.val < 3790 then
(if i.val < 3789 then
816
else
6525)
else
(if i.val < 3791 then
6526
else
6340))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
4817
else
5867)
else
(if i.val < 3795 then
6564
else
5948))
else
(if i.val < 3798 then
(if i.val < 3797 then
6598
else
6442)
else
(if i.val < 3799 then
6599
else
6600)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
6411
else
6760)
else
(if i.val < 3803 then
5263
else
6761))
else
(if i.val < 3806 then
(if i.val < 3805 then
6762
else
5902)
else
(if i.val < 3807 then
5905
else
6763)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
6764
else
6467)
else
(if i.val < 3811 then
1113
else
6375))
else
(if i.val < 3814 then
(if i.val < 3813 then
6765
else
4484)
else
(if i.val < 3815 then
3843
else
6371)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
6766
else
6767)
else
(if i.val < 3819 then
6768
else
1865))
else
(if i.val < 3822 then
(if i.val < 3821 then
5983
else
6769)
else
(if i.val < 3823 then
3811
else
6098))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
6770
else
6771)
else
(if i.val < 3827 then
6772
else
4765))
else
(if i.val < 3830 then
(if i.val < 3829 then
6602
else
5941)
else
(if i.val < 3831 then
6601
else
6773)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
1583
else
4378)
else
(if i.val < 3835 then
3213
else
3821))
else
(if i.val < 3838 then
(if i.val < 3837 then
1619
else
1731)
else
(if i.val < 3839 then
1620
else
1728))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
5623
else
5841)
else
(if i.val < 3843 then
3823
else
5081))
else
(if i.val < 3846 then
(if i.val < 3845 then
6774
else
6413)
else
(if i.val < 3847 then
2763
else
1354)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
4012
else
5027)
else
(if i.val < 3851 then
1526
else
1726))
else
(if i.val < 3854 then
(if i.val < 3853 then
6327
else
1515)
else
(if i.val < 3855 then
3557
else
827))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
6414
else
6415)
else
(if i.val < 3859 then
4749
else
1617))
else
(if i.val < 3862 then
(if i.val < 3861 then
1616
else
6595)
else
(if i.val < 3863 then
6079
else
3875)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
6410
else
6596)
else
(if i.val < 3867 then
6597
else
4321))
else
(if i.val < 3870 then
(if i.val < 3869 then
5736
else
6330)
else
(if i.val < 3871 then
1278
else
6558)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
4455
else
4557)
else
(if i.val < 3875 then
5192
else
1900))
else
(if i.val < 3878 then
(if i.val < 3877 then
6443
else
3566)
else
(if i.val < 3879 then
1238
else
829)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
838
else
6412)
else
(if i.val < 3883 then
821
else
6397))
else
(if i.val < 3886 then
(if i.val < 3885 then
5563
else
6483)
else
(if i.val < 3887 then
6494
else
5916))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
4748
else
4574)
else
(if i.val < 3891 then
4317
else
6487))
else
(if i.val < 3894 then
(if i.val < 3893 then
6482
else
6461)
else
(if i.val < 3895 then
6495
else
5300)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
855
else
851)
else
(if i.val < 3899 then
6775
else
5283))
else
(if i.val < 3902 then
(if i.val < 3901 then
6776
else
6464)
else
(if i.val < 3903 then
6777
else
1982))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
2831
else
1985)
else
(if i.val < 3907 then
3083
else
3787))
else
(if i.val < 3910 then
(if i.val < 3909 then
1720
else
3207)
else
(if i.val < 3911 then
2723
else
5268)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
3568
else
5518)
else
(if i.val < 3915 then
6778
else
2861))
else
(if i.val < 3918 then
(if i.val < 3917 then
1929
else
6610)
else
(if i.val < 3919 then
3136
else
6779))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
5888
else
6780)
else
(if i.val < 3923 then
6781
else
4413))
else
(if i.val < 3926 then
(if i.val < 3925 then
6782
else
5889)
else
(if i.val < 3927 then
1635
else
3360)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
1641
else
6501)
else
(if i.val < 3931 then
6532
else
6502))
else
(if i.val < 3934 then
(if i.val < 3933 then
3608
else
859)
else
(if i.val < 3935 then
2664
else
1029)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
2887
else
2199)
else
(if i.val < 3939 then
3206
else
6589))
else
(if i.val < 3942 then
(if i.val < 3941 then
4064
else
6783)
else
(if i.val < 3943 then
5573
else
6609)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
6530
else
6613)
else
(if i.val < 3947 then
4402
else
4364))
else
(if i.val < 3950 then
(if i.val < 3949 then
6784
else
6612)
else
(if i.val < 3951 then
6592
else
6529))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
1774
else
902)
else
(if i.val < 3955 then
6507
else
6546))
else
(if i.val < 3958 then
(if i.val < 3957 then
2859
else
4820)
else
(if i.val < 3959 then
6528
else
6527)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
904
else
842)
else
(if i.val < 3963 then
898
else
900))
else
(if i.val < 3966 then
(if i.val < 3965 then
4438
else
871)
else
(if i.val < 3967 then
6533
else
6534)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
6205
else
6537)
else
(if i.val < 3971 then
576
else
3603))
else
(if i.val < 3974 then
(if i.val < 3973 then
3602
else
3222)
else
(if i.val < 3975 then
852
else
4334)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
6541
else
4348)
else
(if i.val < 3979 then
6539
else
6540))
else
(if i.val < 3982 then
(if i.val < 3981 then
1023
else
5259)
else
(if i.val < 3983 then
3553
else
4371))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
561
else
584)
else
(if i.val < 3987 then
1459
else
6547))
else
(if i.val < 3990 then
(if i.val < 3989 then
5944
else
6548)
else
(if i.val < 3991 then
4626
else
6578)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
4714
else
6565)
else
(if i.val < 3995 then
5718
else
6559))
else
(if i.val < 3998 then
(if i.val < 3997 then
4946
else
6579)
else
(if i.val < 3999 then
6581
else
1559)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
831
else
882)
else
(if i.val < 4003 then
883
else
2265))
else
(if i.val < 4006 then
(if i.val < 4005 then
6568
else
6569)
else
(if i.val < 4007 then
5005
else
880)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
4047
else
5032)
else
(if i.val < 4011 then
5028
else
6570))
else
(if i.val < 4014 then
(if i.val < 4013 then
3300
else
6572)
else
(if i.val < 4015 then
6588
else
3903))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
3905
else
6078)
else
(if i.val < 4019 then
5611
else
6096))
else
(if i.val < 4022 then
(if i.val < 4021 then
6591
else
824)
else
(if i.val < 4023 then
810
else
585)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
563
else
458)
else
(if i.val < 4027 then
457
else
5371))
else
(if i.val < 4030 then
(if i.val < 4029 then
5370
else
6604)
else
(if i.val < 4031 then
6605
else
6606))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
6607
else
6608)
else
(if i.val < 4035 then
809
else
811))
else
(if i.val < 4038 then
(if i.val < 4037 then
823
else
448)
else
(if i.val < 4039 then
839
else
840)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
843
else
447)
else
(if i.val < 4043 then
899
else
6506))
else
(if i.val < 4046 then
(if i.val < 4045 then
1778
else
861)
else
(if i.val < 4047 then
3469
else
6520))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
6513
else
863)
else
(if i.val < 4051 then
6514
else
6515))
else
(if i.val < 4054 then
(if i.val < 4053 then
6516
else
6203)
else
(if i.val < 4055 then
6521
else
6522)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
6196
else
5988)
else
(if i.val < 4059 then
6211
else
854))
else
(if i.val < 4062 then
(if i.val < 4061 then
862
else
577)
else
(if i.val < 4063 then
454
else
5317)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
2023
else
2784)
else
(if i.val < 4067 then
853
else
845))
else
(if i.val < 4070 then
(if i.val < 4069 then
850
else
2662)
else
(if i.val < 4071 then
2221
else
4969)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
5043
else
2706)
else
(if i.val < 4075 then
6785
else
3250))
else
(if i.val < 4078 then
(if i.val < 4077 then
4981
else
5026)
else
(if i.val < 4079 then
2200
else
3980))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
2193
else
6786)
else
(if i.val < 4083 then
5969
else
2290))
else
(if i.val < 4086 then
(if i.val < 4085 then
1016
else
1718)
else
(if i.val < 4087 then
3190
else
6787)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
1508
else
3149)
else
(if i.val < 4091 then
6788
else
3548))
else
(if i.val < 4094 then
(if i.val < 4093 then
6789
else
4795)
else
(if i.val < 4095 then
6790
else
6791)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0008 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4352 then
(if i.val < 4224 then
(if i.val < 4160 then
(if i.val < 4128 then
(if i.val < 4112 then
(if i.val < 4104 then
(if i.val < 4100 then
(if i.val < 4098 then
(if i.val < 4097 then
3223
else
6644)
else
(if i.val < 4099 then
4848
else
6792))
else
(if i.val < 4102 then
(if i.val < 4101 then
6638
else
6637)
else
(if i.val < 4103 then
5531
else
5533)))
else
(if i.val < 4108 then
(if i.val < 4106 then
(if i.val < 4105 then
5070
else
5381)
else
(if i.val < 4107 then
3314
else
6793))
else
(if i.val < 4110 then
(if i.val < 4109 then
5529
else
2698)
else
(if i.val < 4111 then
3257
else
5532))))
else
(if i.val < 4120 then
(if i.val < 4116 then
(if i.val < 4114 then
(if i.val < 4113 then
2621
else
3810)
else
(if i.val < 4115 then
5397
else
2589))
else
(if i.val < 4118 then
(if i.val < 4117 then
6794
else
3361)
else
(if i.val < 4119 then
2619
else
6795)))
else
(if i.val < 4124 then
(if i.val < 4122 then
(if i.val < 4121 then
4938
else
1200)
else
(if i.val < 4123 then
1921
else
2593))
else
(if i.val < 4126 then
(if i.val < 4125 then
6796
else
6622)
else
(if i.val < 4127 then
4872
else
4932)))))
else
(if i.val < 4144 then
(if i.val < 4136 then
(if i.val < 4132 then
(if i.val < 4130 then
(if i.val < 4129 then
4887
else
6797)
else
(if i.val < 4131 then
5197
else
6798))
else
(if i.val < 4134 then
(if i.val < 4133 then
2797
else
5827)
else
(if i.val < 4135 then
6799
else
5540)))
else
(if i.val < 4140 then
(if i.val < 4138 then
(if i.val < 4137 then
6575
else
4859)
else
(if i.val < 4139 then
3209
else
6800))
else
(if i.val < 4142 then
(if i.val < 4141 then
6801
else
6802)
else
(if i.val < 4143 then
2590
else
6477))))
else
(if i.val < 4152 then
(if i.val < 4148 then
(if i.val < 4146 then
(if i.val < 4145 then
6803
else
2545)
else
(if i.val < 4147 then
4499
else
6804))
else
(if i.val < 4150 then
(if i.val < 4149 then
6805
else
6127)
else
(if i.val < 4151 then
3309
else
6806)))
else
(if i.val < 4156 then
(if i.val < 4154 then
(if i.val < 4153 then
6807
else
2606)
else
(if i.val < 4155 then
2573
else
3254))
else
(if i.val < 4158 then
(if i.val < 4157 then
6808
else
6072)
else
(if i.val < 4159 then
6809
else
6810))))))
else
(if i.val < 4192 then
(if i.val < 4176 then
(if i.val < 4168 then
(if i.val < 4164 then
(if i.val < 4162 then
(if i.val < 4161 then
3547
else
6811)
else
(if i.val < 4163 then
6812
else
6813))
else
(if i.val < 4166 then
(if i.val < 4165 then
5604
else
6814)
else
(if i.val < 4167 then
6434
else
6815)))
else
(if i.val < 4172 then
(if i.val < 4170 then
(if i.val < 4169 then
4821
else
5706)
else
(if i.val < 4171 then
5095
else
6816))
else
(if i.val < 4174 then
(if i.val < 4173 then
5711
else
6817)
else
(if i.val < 4175 then
2336
else
6385))))
else
(if i.val < 4184 then
(if i.val < 4180 then
(if i.val < 4178 then
(if i.val < 4177 then
5951
else
6147)
else
(if i.val < 4179 then
4356
else
3411))
else
(if i.val < 4182 then
(if i.val < 4181 then
5869
else
6636)
else
(if i.val < 4183 then
5262
else
6818)))
else
(if i.val < 4188 then
(if i.val < 4186 then
(if i.val < 4185 then
6635
else
4926)
else
(if i.val < 4187 then
5890
else
6126))
else
(if i.val < 4190 then
(if i.val < 4189 then
6819
else
5323)
else
(if i.val < 4191 then
3252
else
4706)))))
else
(if i.val < 4208 then
(if i.val < 4200 then
(if i.val < 4196 then
(if i.val < 4194 then
(if i.val < 4193 then
5669
else
1151)
else
(if i.val < 4195 then
1239
else
6820))
else
(if i.val < 4198 then
(if i.val < 4197 then
6821
else
6822)
else
(if i.val < 4199 then
3669
else
6823)))
else
(if i.val < 4204 then
(if i.val < 4202 then
(if i.val < 4201 then
2929
else
3819)
else
(if i.val < 4203 then
6824
else
3408))
else
(if i.val < 4206 then
(if i.val < 4205 then
5194
else
6825)
else
(if i.val < 4207 then
5958
else
2360))))
else
(if i.val < 4216 then
(if i.val < 4212 then
(if i.val < 4210 then
(if i.val < 4209 then
6826
else
6827)
else
(if i.val < 4211 then
1449
else
6634))
else
(if i.val < 4214 then
(if i.val < 4213 then
6828
else
2487)
else
(if i.val < 4215 then
6829
else
6830)))
else
(if i.val < 4220 then
(if i.val < 4218 then
(if i.val < 4217 then
6643
else
6085)
else
(if i.val < 4219 then
4340
else
6624))
else
(if i.val < 4222 then
(if i.val < 4221 then
4322
else
5352)
else
(if i.val < 4223 then
1525
else
3600)))))))
else
(if i.val < 4288 then
(if i.val < 4256 then
(if i.val < 4240 then
(if i.val < 4232 then
(if i.val < 4228 then
(if i.val < 4226 then
(if i.val < 4225 then
2268
else
5387)
else
(if i.val < 4227 then
6629
else
3245))
else
(if i.val < 4230 then
(if i.val < 4229 then
6625
else
423)
else
(if i.val < 4231 then
424
else
425)))
else
(if i.val < 4236 then
(if i.val < 4234 then
(if i.val < 4233 then
431
else
432)
else
(if i.val < 4235 then
433
else
434))
else
(if i.val < 4238 then
(if i.val < 4237 then
443
else
446)
else
(if i.val < 4239 then
449
else
450))))
else
(if i.val < 4248 then
(if i.val < 4244 then
(if i.val < 4242 then
(if i.val < 4241 then
451
else
453)
else
(if i.val < 4243 then
463
else
500))
else
(if i.val < 4246 then
(if i.val < 4245 then
501
else
502)
else
(if i.val < 4247 then
503
else
505)))
else
(if i.val < 4252 then
(if i.val < 4250 then
(if i.val < 4249 then
507
else
508)
else
(if i.val < 4251 then
509
else
517))
else
(if i.val < 4254 then
(if i.val < 4253 then
519
else
520)
else
(if i.val < 4255 then
521
else
522)))))
else
(if i.val < 4272 then
(if i.val < 4264 then
(if i.val < 4260 then
(if i.val < 4258 then
(if i.val < 4257 then
524
else
525)
else
(if i.val < 4259 then
526
else
527))
else
(if i.val < 4262 then
(if i.val < 4261 then
530
else
531)
else
(if i.val < 4263 then
532
else
537)))
else
(if i.val < 4268 then
(if i.val < 4266 then
(if i.val < 4265 then
553
else
555)
else
(if i.val < 4267 then
557
else
558))
else
(if i.val < 4270 then
(if i.val < 4269 then
560
else
562)
else
(if i.val < 4271 then
568
else
570))))
else
(if i.val < 4280 then
(if i.val < 4276 then
(if i.val < 4274 then
(if i.val < 4273 then
571
else
572)
else
(if i.val < 4275 then
573
else
575))
else
(if i.val < 4278 then
(if i.val < 4277 then
581
else
595)
else
(if i.val < 4279 then
596
else
807)))
else
(if i.val < 4284 then
(if i.val < 4282 then
(if i.val < 4281 then
813
else
814)
else
(if i.val < 4283 then
817
else
818))
else
(if i.val < 4286 then
(if i.val < 4285 then
819
else
822)
else
(if i.val < 4287 then
844
else
846))))))
else
(if i.val < 4320 then
(if i.val < 4304 then
(if i.val < 4296 then
(if i.val < 4292 then
(if i.val < 4290 then
(if i.val < 4289 then
847
else
848)
else
(if i.val < 4291 then
849
else
5131))
else
(if i.val < 4294 then
(if i.val < 4293 then
7208
else
2476)
else
(if i.val < 4295 then
3791
else
3114)))
else
(if i.val < 4300 then
(if i.val < 4298 then
(if i.val < 4297 then
7401
else
3231)
else
(if i.val < 4299 then
5746
else
8151))
else
(if i.val < 4302 then
(if i.val < 4301 then
1034
else
2189)
else
(if i.val < 4303 then
4448
else
2204))))
else
(if i.val < 4312 then
(if i.val < 4308 then
(if i.val < 4306 then
(if i.val < 4305 then
2913
else
2904)
else
(if i.val < 4307 then
7859
else
7883))
else
(if i.val < 4310 then
(if i.val < 4309 then
2372
else
1370)
else
(if i.val < 4311 then
7676
else
5506)))
else
(if i.val < 4316 then
(if i.val < 4314 then
(if i.val < 4313 then
5515
else
8152)
else
(if i.val < 4315 then
7804
else
2919))
else
(if i.val < 4318 then
(if i.val < 4317 then
3937
else
3449)
else
(if i.val < 4319 then
3179
else
6450)))))
else
(if i.val < 4336 then
(if i.val < 4328 then
(if i.val < 4324 then
(if i.val < 4322 then
(if i.val < 4321 then
988
else
1896)
else
(if i.val < 4323 then
1936
else
6863))
else
(if i.val < 4326 then
(if i.val < 4325 then
2289
else
6440)
else
(if i.val < 4327 then
6866
else
6867)))
else
(if i.val < 4332 then
(if i.val < 4330 then
(if i.val < 4329 then
4325
else
4461)
else
(if i.val < 4331 then
7734
else
6909))
else
(if i.val < 4334 then
(if i.val < 4333 then
8153
else
7141)
else
(if i.val < 4335 then
1975
else
1976))))
else
(if i.val < 4344 then
(if i.val < 4340 then
(if i.val < 4338 then
(if i.val < 4337 then
4834
else
4408)
else
(if i.val < 4339 then
5824
else
7050))
else
(if i.val < 4342 then
(if i.val < 4341 then
1934
else
6880)
else
(if i.val < 4343 then
6881
else
6882)))
else
(if i.val < 4348 then
(if i.val < 4346 then
(if i.val < 4345 then
2588
else
3346)
else
(if i.val < 4347 then
3356
else
4387))
else
(if i.val < 4350 then
(if i.val < 4349 then
6916
else
2230)
else
(if i.val < 4351 then
7915
else
2249))))))))
else
(if i.val < 4480 then
(if i.val < 4416 then
(if i.val < 4384 then
(if i.val < 4368 then
(if i.val < 4360 then
(if i.val < 4356 then
(if i.val < 4354 then
(if i.val < 4353 then
7916
else
3978)
else
(if i.val < 4355 then
7732
else
2491))
else
(if i.val < 4358 then
(if i.val < 4357 then
1330
else
7133)
else
(if i.val < 4359 then
8029
else
8030)))
else
(if i.val < 4364 then
(if i.val < 4362 then
(if i.val < 4361 then
8031
else
8032)
else
(if i.val < 4363 then
8033
else
8131))
else
(if i.val < 4366 then
(if i.val < 4365 then
7561
else
7905)
else
(if i.val < 4367 then
8132
else
8133))))
else
(if i.val < 4376 then
(if i.val < 4372 then
(if i.val < 4370 then
(if i.val < 4369 then
8134
else
8095)
else
(if i.val < 4371 then
6140
else
1973))
else
(if i.val < 4374 then
(if i.val < 4373 then
5305
else
4900)
else
(if i.val < 4375 then
2595
else
8135)))
else
(if i.val < 4380 then
(if i.val < 4378 then
(if i.val < 4377 then
2400
else
3389)
else
(if i.val < 4379 then
7985
else
7984))
else
(if i.val < 4382 then
(if i.val < 4381 then
5910
else
5945)
else
(if i.val < 4383 then
3641
else
3934)))))
else
(if i.val < 4400 then
(if i.val < 4392 then
(if i.val < 4388 then
(if i.val < 4386 then
(if i.val < 4385 then
7709
else
8287)
else
(if i.val < 4387 then
7848
else
8288))
else
(if i.val < 4390 then
(if i.val < 4389 then
5088
else
2475)
else
(if i.val < 4391 then
8107
else
7129)))
else
(if i.val < 4396 then
(if i.val < 4394 then
(if i.val < 4393 then
5049
else
7981)
else
(if i.val < 4395 then
8289
else
7876))
else
(if i.val < 4398 then
(if i.val < 4397 then
6428
else
7712)
else
(if i.val < 4399 then
6474
else
5065))))
else
(if i.val < 4408 then
(if i.val < 4404 then
(if i.val < 4402 then
(if i.val < 4401 then
8290
else
1535)
else
(if i.val < 4403 then
6948
else
8291))
else
(if i.val < 4406 then
(if i.val < 4405 then
4416
else
7502)
else
(if i.val < 4407 then
5728
else
1623)))
else
(if i.val < 4412 then
(if i.val < 4410 then
(if i.val < 4409 then
8014
else
8292)
else
(if i.val < 4411 then
6986
else
5112))
else
(if i.val < 4414 then
(if i.val < 4413 then
6962
else
5737)
else
(if i.val < 4415 then
2263
else
5754))))))
else
(if i.val < 4448 then
(if i.val < 4432 then
(if i.val < 4424 then
(if i.val < 4420 then
(if i.val < 4418 then
(if i.val < 4417 then
5745
else
7080)
else
(if i.val < 4419 then
5818
else
7926))
else
(if i.val < 4422 then
(if i.val < 4421 then
2523
else
5335)
else
(if i.val < 4423 then
3437
else
3355)))
else
(if i.val < 4428 then
(if i.val < 4426 then
(if i.val < 4425 then
7783
else
2279)
else
(if i.val < 4427 then
2276
else
5973))
else
(if i.val < 4430 then
(if i.val < 4429 then
5384
else
5955)
else
(if i.val < 4431 then
1018
else
7675))))
else
(if i.val < 4440 then
(if i.val < 4436 then
(if i.val < 4434 then
(if i.val < 4433 then
5280
else
4319)
else
(if i.val < 4435 then
1590
else
7966))
else
(if i.val < 4438 then
(if i.val < 4437 then
8293
else
2472)
else
(if i.val < 4439 then
2300
else
1609)))
else
(if i.val < 4444 then
(if i.val < 4442 then
(if i.val < 4441 then
7929
else
2211)
else
(if i.val < 4443 then
5701
else
6989))
else
(if i.val < 4446 then
(if i.val < 4445 then
6842
else
7069)
else
(if i.val < 4447 then
7795
else
990)))))
else
(if i.val < 4464 then
(if i.val < 4456 then
(if i.val < 4452 then
(if i.val < 4450 then
(if i.val < 4449 then
6441
else
8294)
else
(if i.val < 4451 then
6562
else
2192))
else
(if i.val < 4454 then
(if i.val < 4453 then
3303
else
2207)
else
(if i.val < 4455 then
7300
else
3302)))
else
(if i.val < 4460 then
(if i.val < 4458 then
(if i.val < 4457 then
4305
else
5739)
else
(if i.val < 4459 then
8295
else
7741))
else
(if i.val < 4462 then
(if i.val < 4461 then
7957
else
6987)
else
(if i.val < 4463 then
6843
else
2682))))
else
(if i.val < 4472 then
(if i.val < 4468 then
(if i.val < 4466 then
(if i.val < 4465 then
7191
else
7008)
else
(if i.val < 4467 then
5234
else
7786))
else
(if i.val < 4470 then
(if i.val < 4469 then
7995
else
7504)
else
(if i.val < 4471 then
3087
else
5826)))
else
(if i.val < 4476 then
(if i.val < 4474 then
(if i.val < 4473 then
4355
else
6973)
else
(if i.val < 4475 then
7004
else
7005))
else
(if i.val < 4478 then
(if i.val < 4477 then
7006
else
6183)
else
(if i.val < 4479 then
8296
else
7190)))))))
else
(if i.val < 4544 then
(if i.val < 4512 then
(if i.val < 4496 then
(if i.val < 4488 then
(if i.val < 4484 then
(if i.val < 4482 then
(if i.val < 4481 then
2646
else
7558)
else
(if i.val < 4483 then
4546
else
5866))
else
(if i.val < 4486 then
(if i.val < 4485 then
5368
else
2920)
else
(if i.val < 4487 then
6934
else
7031)))
else
(if i.val < 4492 then
(if i.val < 4490 then
(if i.val < 4489 then
5168
else
7715)
else
(if i.val < 4491 then
7016
else
1308))
else
(if i.val < 4494 then
(if i.val < 4493 then
5193
else
1287)
else
(if i.val < 4495 then
7334
else
2282))))
else
(if i.val < 4504 then
(if i.val < 4500 then
(if i.val < 4498 then
(if i.val < 4497 then
8021
else
1296)
else
(if i.val < 4499 then
8005
else
1236))
else
(if i.val < 4502 then
(if i.val < 4501 then
7452
else
7556)
else
(if i.val < 4503 then
6959
else
3082)))
else
(if i.val < 4508 then
(if i.val < 4506 then
(if i.val < 4505 then
2489
else
1221)
else
(if i.val < 4507 then
4860
else
7027))
else
(if i.val < 4510 then
(if i.val < 4509 then
6453
else
5547)
else
(if i.val < 4511 then
1283
else
7189)))))
else
(if i.val < 4528 then
(if i.val < 4520 then
(if i.val < 4516 then
(if i.val < 4514 then
(if i.val < 4513 then
5336
else
6198)
else
(if i.val < 4515 then
3103
else
3085))
else
(if i.val < 4518 then
(if i.val < 4517 then
2912
else
7239)
else
(if i.val < 4519 then
2843
else
7574)))
else
(if i.val < 4524 then
(if i.val < 4522 then
(if i.val < 4521 then
7043
else
1307)
else
(if i.val < 4523 then
7538
else
8197))
else
(if i.val < 4526 then
(if i.val < 4525 then
5229
else
6632)
else
(if i.val < 4527 then
7257
else
4561))))
else
(if i.val < 4536 then
(if i.val < 4532 then
(if i.val < 4530 then
(if i.val < 4529 then
5294
else
7764)
else
(if i.val < 4531 then
6111
else
5943))
else
(if i.val < 4534 then
(if i.val < 4533 then
6633
else
2876)
else
(if i.val < 4535 then
7453
else
5545)))
else
(if i.val < 4540 then
(if i.val < 4538 then
(if i.val < 4537 then
5375
else
7601)
else
(if i.val < 4539 then
3780
else
6939))
else
(if i.val < 4542 then
(if i.val < 4541 then
2792
else
7927)
else
(if i.val < 4543 then
7068
else
5571))))))
else
(if i.val < 4576 then
(if i.val < 4560 then
(if i.val < 4552 then
(if i.val < 4548 then
(if i.val < 4546 then
(if i.val < 4545 then
6922
else
7772)
else
(if i.val < 4547 then
6400
else
7785))
else
(if i.val < 4550 then
(if i.val < 4549 then
8273
else
4359)
else
(if i.val < 4551 then
2701
else
1317)))
else
(if i.val < 4556 then
(if i.val < 4554 then
(if i.val < 4553 then
989
else
5199)
else
(if i.val < 4555 then
6958
else
8244))
else
(if i.val < 4558 then
(if i.val < 4557 then
6617
else
7074)
else
(if i.val < 4559 then
3301
else
2832))))
else
(if i.val < 4568 then
(if i.val < 4564 then
(if i.val < 4562 then
(if i.val < 4561 then
2508
else
7898)
else
(if i.val < 4563 then
8297
else
5185))
else
(if i.val < 4566 then
(if i.val < 4565 then
5275
else
5220)
else
(if i.val < 4567 then
2686
else
5844)))
else
(if i.val < 4572 then
(if i.val < 4570 then
(if i.val < 4569 then
3244
else
8023)
else
(if i.val < 4571 then
5843
else
5845))
else
(if i.val < 4574 then
(if i.val < 4573 then
3359
else
7557)
else
(if i.val < 4575 then
8279
else
5593)))))
else
(if i.val < 4592 then
(if i.val < 4584 then
(if i.val < 4580 then
(if i.val < 4578 then
(if i.val < 4577 then
7173
else
7901)
else
(if i.val < 4579 then
8145
else
7384))
else
(if i.val < 4582 then
(if i.val < 4581 then
5809
else
4759)
else
(if i.val < 4583 then
5962
else
5136)))
else
(if i.val < 4588 then
(if i.val < 4586 then
(if i.val < 4585 then
6457
else
7195)
else
(if i.val < 4587 then
7194
else
3779))
else
(if i.val < 4590 then
(if i.val < 4589 then
4767
else
4858)
else
(if i.val < 4591 then
7728
else
6425))))
else
(if i.val < 4600 then
(if i.val < 4596 then
(if i.val < 4594 then
(if i.val < 4593 then
7546
else
4867)
else
(if i.val < 4595 then
2654
else
6999))
else
(if i.val < 4598 then
(if i.val < 4597 then
6884
else
7722)
else
(if i.val < 4599 then
3815
else
6551)))
else
(if i.val < 4604 then
(if i.val < 4602 then
(if i.val < 4601 then
7185
else
8042)
else
(if i.val < 4603 then
8274
else
8267))
else
(if i.val < 4606 then
(if i.val < 4605 then
5538
else
2250)
else
(if i.val < 4607 then
7815
else
2770)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0009 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 4864 then
(if i.val < 4736 then
(if i.val < 4672 then
(if i.val < 4640 then
(if i.val < 4624 then
(if i.val < 4616 then
(if i.val < 4612 then
(if i.val < 4610 then
(if i.val < 4609 then
3785
else
7115)
else
(if i.val < 4611 then
1082
else
6577))
else
(if i.val < 4614 then
(if i.val < 4613 then
7144
else
8298)
else
(if i.val < 4615 then
2550
else
7192)))
else
(if i.val < 4620 then
(if i.val < 4618 then
(if i.val < 4617 then
1170
else
4865)
else
(if i.val < 4619 then
4861
else
6878))
else
(if i.val < 4622 then
(if i.val < 4621 then
8002
else
5154)
else
(if i.val < 4623 then
8188
else
4457))))
else
(if i.val < 4632 then
(if i.val < 4628 then
(if i.val < 4626 then
(if i.val < 4625 then
8261
else
8113)
else
(if i.val < 4627 then
6185
else
7124))
else
(if i.val < 4630 then
(if i.val < 4629 then
7125
else
8299)
else
(if i.val < 4631 then
8091
else
5699)))
else
(if i.val < 4636 then
(if i.val < 4634 then
(if i.val < 4633 then
7132
else
4503)
else
(if i.val < 4635 then
7137
else
4470))
else
(if i.val < 4638 then
(if i.val < 4637 then
1441
else
1442)
else
(if i.val < 4639 then
7146
else
7147)))))
else
(if i.val < 4656 then
(if i.val < 4648 then
(if i.val < 4644 then
(if i.val < 4642 then
(if i.val < 4641 then
7148
else
5968)
else
(if i.val < 4643 then
6325
else
5244))
else
(if i.val < 4646 then
(if i.val < 4645 then
1446
else
7143)
else
(if i.val < 4647 then
1444
else
1445)))
else
(if i.val < 4652 then
(if i.val < 4650 then
(if i.val < 4649 then
1447
else
3372)
else
(if i.val < 4651 then
4855
else
2939))
else
(if i.val < 4654 then
(if i.val < 4653 then
7152
else
5178)
else
(if i.val < 4655 then
6406
else
5170))))
else
(if i.val < 4664 then
(if i.val < 4660 then
(if i.val < 4658 then
(if i.val < 4657 then
5733
else
2842)
else
(if i.val < 4659 then
7713
else
2808))
else
(if i.val < 4662 then
(if i.val < 4661 then
7159
else
3228)
else
(if i.val < 4663 then
7724
else
7600)))
else
(if i.val < 4668 then
(if i.val < 4666 then
(if i.val < 4665 then
4514
else
7726)
else
(if i.val < 4667 then
7727
else
6475))
else
(if i.val < 4670 then
(if i.val < 4669 then
7579
else
4485)
else
(if i.val < 4671 then
7721
else
7723))))))
else
(if i.val < 4704 then
(if i.val < 4688 then
(if i.val < 4680 then
(if i.val < 4676 then
(if i.val < 4674 then
(if i.val < 4673 then
2963
else
1148)
else
(if i.val < 4675 then
8300
else
7462))
else
(if i.val < 4678 then
(if i.val < 4677 then
8148
else
8036)
else
(if i.val < 4679 then
4603
else
5191)))
else
(if i.val < 4684 then
(if i.val < 4682 then
(if i.val < 4681 then
6925
else
5865)
else
(if i.val < 4683 then
7514
else
7284))
else
(if i.val < 4686 then
(if i.val < 4685 then
5240
else
7432)
else
(if i.val < 4687 then
3527
else
8234))))
else
(if i.val < 4696 then
(if i.val < 4692 then
(if i.val < 4690 then
(if i.val < 4689 then
4545
else
8301)
else
(if i.val < 4691 then
1120
else
1086))
else
(if i.val < 4694 then
(if i.val < 4693 then
1122
else
1087)
else
(if i.val < 4695 then
4739
else
4774)))
else
(if i.val < 4700 then
(if i.val < 4698 then
(if i.val < 4697 then
4793
else
2707)
else
(if i.val < 4699 then
7188
else
4826))
else
(if i.val < 4702 then
(if i.val < 4701 then
6493
else
5600)
else
(if i.val < 4703 then
4389
else
5215)))))
else
(if i.val < 4720 then
(if i.val < 4712 then
(if i.val < 4708 then
(if i.val < 4706 then
(if i.val < 4705 then
6983
else
6496)
else
(if i.val < 4707 then
1848
else
7193))
else
(if i.val < 4710 then
(if i.val < 4709 then
4618
else
6910)
else
(if i.val < 4711 then
4825
else
4921)))
else
(if i.val < 4716 then
(if i.val < 4714 then
(if i.val < 4713 then
7200
else
3109)
else
(if i.val < 4715 then
7629
else
7201))
else
(if i.val < 4718 then
(if i.val < 4717 then
1711
else
7353)
else
(if i.val < 4719 then
5132
else
7203))))
else
(if i.val < 4728 then
(if i.val < 4724 then
(if i.val < 4722 then
(if i.val < 4721 then
2385
else
7106)
else
(if i.val < 4723 then
1753
else
5586))
else
(if i.val < 4726 then
(if i.val < 4725 then
2243
else
6903)
else
(if i.val < 4727 then
5816
else
2257)))
else
(if i.val < 4732 then
(if i.val < 4730 then
(if i.val < 4729 then
7166
else
7472)
else
(if i.val < 4731 then
2231
else
6940))
else
(if i.val < 4734 then
(if i.val < 4733 then
7982
else
3122)
else
(if i.val < 4735 then
2898
else
7316)))))))
else
(if i.val < 4800 then
(if i.val < 4768 then
(if i.val < 4752 then
(if i.val < 4744 then
(if i.val < 4740 then
(if i.val < 4738 then
(if i.val < 4737 then
4579
else
8038)
else
(if i.val < 4739 then
5041
else
2328))
else
(if i.val < 4742 then
(if i.val < 4741 then
5594
else
2524)
else
(if i.val < 4743 then
7599
else
7315)))
else
(if i.val < 4748 then
(if i.val < 4746 then
(if i.val < 4745 then
5954
else
1691)
else
(if i.val < 4747 then
4685
else
7821))
else
(if i.val < 4750 then
(if i.val < 4749 then
2329
else
7983)
else
(if i.val < 4751 then
1518
else
7582))))
else
(if i.val < 4760 then
(if i.val < 4756 then
(if i.val < 4754 then
(if i.val < 4753 then
7001
else
2527)
else
(if i.val < 4755 then
2198
else
7611))
else
(if i.val < 4758 then
(if i.val < 4757 then
7951
else
5740)
else
(if i.val < 4759 then
7950
else
3090)))
else
(if i.val < 4764 then
(if i.val < 4762 then
(if i.val < 4761 then
1054
else
2379)
else
(if i.val < 4763 then
1312
else
7231))
else
(if i.val < 4766 then
(if i.val < 4765 then
7232
else
4934)
else
(if i.val < 4767 then
7313
else
7314)))))
else
(if i.val < 4784 then
(if i.val < 4776 then
(if i.val < 4772 then
(if i.val < 4770 then
(if i.val < 4769 then
3186
else
7238)
else
(if i.val < 4771 then
7948
else
7949))
else
(if i.val < 4774 then
(if i.val < 4773 then
5950
else
7310)
else
(if i.val < 4775 then
2304
else
8154)))
else
(if i.val < 4780 then
(if i.val < 4778 then
(if i.val < 4777 then
3456
else
6071)
else
(if i.val < 4779 then
6336
else
3900))
else
(if i.val < 4782 then
(if i.val < 4781 then
8155
else
6449)
else
(if i.val < 4783 then
5024
else
5894))))
else
(if i.val < 4792 then
(if i.val < 4788 then
(if i.val < 4786 then
(if i.val < 4785 then
4464
else
2448)
else
(if i.val < 4787 then
2709
else
8156))
else
(if i.val < 4790 then
(if i.val < 4789 then
2234
else
4509)
else
(if i.val < 4791 then
8157
else
8158)))
else
(if i.val < 4796 then
(if i.val < 4794 then
(if i.val < 4793 then
7780
else
2309)
else
(if i.val < 4795 then
7890
else
1055))
else
(if i.val < 4798 then
(if i.val < 4797 then
6077
else
6351)
else
(if i.val < 4799 then
6354
else
7030))))))
else
(if i.val < 4832 then
(if i.val < 4816 then
(if i.val < 4808 then
(if i.val < 4804 then
(if i.val < 4802 then
(if i.val < 4801 then
4502
else
5861)
else
(if i.val < 4803 then
4370
else
6346))
else
(if i.val < 4806 then
(if i.val < 4805 then
7076
else
7866)
else
(if i.val < 4807 then
5553
else
6074)))
else
(if i.val < 4812 then
(if i.val < 4810 then
(if i.val < 4809 then
3429
else
5018)
else
(if i.val < 4811 then
7917
else
7918))
else
(if i.val < 4814 then
(if i.val < 4813 then
3403
else
6844)
else
(if i.val < 4815 then
7577
else
2725))))
else
(if i.val < 4824 then
(if i.val < 4820 then
(if i.val < 4818 then
(if i.val < 4817 then
5332
else
2684)
else
(if i.val < 4819 then
5521
else
7390))
else
(if i.val < 4822 then
(if i.val < 4821 then
1877
else
1310)
else
(if i.val < 4823 then
3784
else
2755)))
else
(if i.val < 4828 then
(if i.val < 4826 then
(if i.val < 4825 then
7719
else
2614)
else
(if i.val < 4827 then
2473
else
7046))
else
(if i.val < 4830 then
(if i.val < 4829 then
995
else
6886)
else
(if i.val < 4831 then
6887
else
6343)))))
else
(if i.val < 4848 then
(if i.val < 4840 then
(if i.val < 4836 then
(if i.val < 4834 then
(if i.val < 4833 then
3397
else
6888)
else
(if i.val < 4835 then
6850
else
1161))
else
(if i.val < 4838 then
(if i.val < 4837 then
1162
else
1163)
else
(if i.val < 4839 then
3367
else
3323)))
else
(if i.val < 4844 then
(if i.val < 4842 then
(if i.val < 4841 then
7285
else
7286)
else
(if i.val < 4843 then
5840
else
4968))
else
(if i.val < 4846 then
(if i.val < 4845 then
4421
else
2648)
else
(if i.val < 4847 then
5039
else
1336))))
else
(if i.val < 4856 then
(if i.val < 4852 then
(if i.val < 4850 then
(if i.val < 4849 then
1068
else
4483)
else
(if i.val < 4851 then
6420
else
5067))
else
(if i.val < 4854 then
(if i.val < 4853 then
5202
else
6421)
else
(if i.val < 4855 then
7121
else
2677)))
else
(if i.val < 4860 then
(if i.val < 4858 then
(if i.val < 4857 then
2514
else
6919)
else
(if i.val < 4859 then
6920
else
1226))
else
(if i.val < 4862 then
(if i.val < 4861 then
7214
else
4708)
else
(if i.val < 4863 then
7761
else
7817))))))))
else
(if i.val < 4992 then
(if i.val < 4928 then
(if i.val < 4896 then
(if i.val < 4880 then
(if i.val < 4872 then
(if i.val < 4868 then
(if i.val < 4866 then
(if i.val < 4865 then
1169
else
4918)
else
(if i.val < 4867 then
5881
else
7850))
else
(if i.val < 4870 then
(if i.val < 4869 then
4877
else
5045)
else
(if i.val < 4871 then
2585
else
4896)))
else
(if i.val < 4876 then
(if i.val < 4874 then
(if i.val < 4873 then
1199
else
3070)
else
(if i.val < 4875 then
4961
else
6561))
else
(if i.val < 4878 then
(if i.val < 4877 then
2620
else
4939)
else
(if i.val < 4879 then
8034
else
7240))))
else
(if i.val < 4888 then
(if i.val < 4884 then
(if i.val < 4882 then
(if i.val < 4881 then
5176
else
8250)
else
(if i.val < 4883 then
7140
else
7361))
else
(if i.val < 4886 then
(if i.val < 4885 then
4829
else
8302)
else
(if i.val < 4887 then
5807
else
1205)))
else
(if i.val < 4892 then
(if i.val < 4890 then
(if i.val < 4889 then
7515
else
4830)
else
(if i.val < 4891 then
2591
else
2582))
else
(if i.val < 4894 then
(if i.val < 4893 then
2628
else
5904)
else
(if i.val < 4895 then
3642
else
2605)))))
else
(if i.val < 4912 then
(if i.val < 4904 then
(if i.val < 4900 then
(if i.val < 4898 then
(if i.val < 4897 then
7280
else
7973)
else
(if i.val < 4899 then
2612
else
2238))
else
(if i.val < 4902 then
(if i.val < 4901 then
5536
else
7623)
else
(if i.val < 4903 then
6858
else
7198)))
else
(if i.val < 4908 then
(if i.val < 4906 then
(if i.val < 4905 then
7149
else
2302)
else
(if i.val < 4907 then
1451
else
4607))
else
(if i.val < 4910 then
(if i.val < 4909 then
2380
else
7341)
else
(if i.val < 4911 then
7350
else
7733))))
else
(if i.val < 4920 then
(if i.val < 4916 then
(if i.val < 4914 then
(if i.val < 4913 then
2743
else
4904)
else
(if i.val < 4915 then
8303
else
6102))
else
(if i.val < 4918 then
(if i.val < 4917 then
2838
else
4773)
else
(if i.val < 4919 then
4617
else
7823)))
else
(if i.val < 4924 then
(if i.val < 4922 then
(if i.val < 4921 then
8238
else
2828)
else
(if i.val < 4923 then
7359
else
2581))
else
(if i.val < 4926 then
(if i.val < 4925 then
4929
else
3606)
else
(if i.val < 4927 then
1343
else
8304))))))
else
(if i.val < 4960 then
(if i.val < 4944 then
(if i.val < 4936 then
(if i.val < 4932 then
(if i.val < 4930 then
(if i.val < 4929 then
6364
else
2622)
else
(if i.val < 4931 then
6439
else
8305))
else
(if i.val < 4934 then
(if i.val < 4933 then
1201
else
4876)
else
(if i.val < 4935 then
3827
else
1284)))
else
(if i.val < 4940 then
(if i.val < 4938 then
(if i.val < 4937 then
1192
else
3064)
else
(if i.val < 4939 then
1188
else
4868))
else
(if i.val < 4942 then
(if i.val < 4941 then
7360
else
4892)
else
(if i.val < 4943 then
2583
else
8109))))
else
(if i.val < 4952 then
(if i.val < 4948 then
(if i.val < 4946 then
(if i.val < 4945 then
2592
else
2596)
else
(if i.val < 4947 then
6618
else
5720))
else
(if i.val < 4950 then
(if i.val < 4949 then
7370
else
1196)
else
(if i.val < 4951 then
7375
else
5346)))
else
(if i.val < 4956 then
(if i.val < 4954 then
(if i.val < 4953 then
4363
else
4944)
else
(if i.val < 4955 then
7666
else
2227))
else
(if i.val < 4958 then
(if i.val < 4957 then
6926
else
6927)
else
(if i.val < 4959 then
7544
else
5156)))))
else
(if i.val < 4976 then
(if i.val < 4968 then
(if i.val < 4964 then
(if i.val < 4962 then
(if i.val < 4961 then
4888
else
3567)
else
(if i.val < 4963 then
4386
else
5093))
else
(if i.val < 4966 then
(if i.val < 4965 then
7348
else
2678)
else
(if i.val < 4967 then
2232
else
2242)))
else
(if i.val < 4972 then
(if i.val < 4970 then
(if i.val < 4969 then
3342
else
1006)
else
(if i.val < 4971 then
2229
else
6932))
else
(if i.val < 4974 then
(if i.val < 4973 then
1614
else
3400)
else
(if i.val < 4975 then
8265
else
2903))))
else
(if i.val < 4984 then
(if i.val < 4980 then
(if i.val < 4978 then
(if i.val < 4977 then
3354
else
3320)
else
(if i.val < 4979 then
1207
else
4594))
else
(if i.val < 4982 then
(if i.val < 4981 then
7396
else
1011)
else
(if i.val < 4983 then
5535
else
4394)))
else
(if i.val < 4988 then
(if i.val < 4986 then
(if i.val < 4985 then
4398
else
5549)
else
(if i.val < 4987 then
7397
else
1265))
else
(if i.val < 4990 then
(if i.val < 4989 then
7400
else
3846)
else
(if i.val < 4991 then
2477
else
1528)))))))
else
(if i.val < 5056 then
(if i.val < 5024 then
(if i.val < 5008 then
(if i.val < 5000 then
(if i.val < 4996 then
(if i.val < 4994 then
(if i.val < 4993 then
3217
else
3156)
else
(if i.val < 4995 then
7729
else
5539))
else
(if i.val < 4998 then
(if i.val < 4997 then
7730
else
7731)
else
(if i.val < 4999 then
6942
else
2248)))
else
(if i.val < 5004 then
(if i.val < 5002 then
(if i.val < 5001 then
2228
else
7094)
else
(if i.val < 5003 then
4372
else
2732))
else
(if i.val < 5006 then
(if i.val < 5005 then
2237
else
5362)
else
(if i.val < 5007 then
6937
else
5534))))
else
(if i.val < 5016 then
(if i.val < 5012 then
(if i.val < 5010 then
(if i.val < 5009 then
6941
else
4396)
else
(if i.val < 5011 then
7663
else
5868))
else
(if i.val < 5014 then
(if i.val < 5013 then
3363
else
2517)
else
(if i.val < 5015 then
2531
else
1644)))
else
(if i.val < 5020 then
(if i.val < 5018 then
(if i.val < 5017 then
3432
else
1613)
else
(if i.val < 5019 then
3321
else
3395))
else
(if i.val < 5022 then
(if i.val < 5021 then
7174
else
5620)
else
(if i.val < 5023 then
5621
else
3221)))))
else
(if i.val < 5040 then
(if i.val < 5032 then
(if i.val < 5028 then
(if i.val < 5026 then
(if i.val < 5025 then
3640
else
4471)
else
(if i.val < 5027 then
1019
else
5696))
else
(if i.val < 5030 then
(if i.val < 5029 then
5871
else
8088)
else
(if i.val < 5031 then
8008
else
2447)))
else
(if i.val < 5036 then
(if i.val < 5034 then
(if i.val < 5033 then
8245
else
3436)
else
(if i.val < 5035 then
7745
else
7435))
else
(if i.val < 5038 then
(if i.val < 5037 then
3427
else
3830)
else
(if i.val < 5039 then
5896
else
3357))))
else
(if i.val < 5048 then
(if i.val < 5044 then
(if i.val < 5042 then
(if i.val < 5041 then
7572
else
7658)
else
(if i.val < 5043 then
7464
else
1007))
else
(if i.val < 5046 then
(if i.val < 5045 then
7340
else
5394)
else
(if i.val < 5047 then
4381
else
1318)))
else
(if i.val < 5052 then
(if i.val < 5050 then
(if i.val < 5049 then
4367
else
2625)
else
(if i.val < 5051 then
7153
else
5741))
else
(if i.val < 5054 then
(if i.val < 5053 then
2251
else
7692)
else
(if i.val < 5055 then
8306
else
2845))))))
else
(if i.val < 5088 then
(if i.val < 5072 then
(if i.val < 5064 then
(if i.val < 5060 then
(if i.val < 5058 then
(if i.val < 5057 then
5729
else
3073)
else
(if i.val < 5059 then
7891
else
7794))
else
(if i.val < 5062 then
(if i.val < 5061 then
7813
else
3801)
else
(if i.val < 5063 then
7057
else
4494)))
else
(if i.val < 5068 then
(if i.val < 5066 then
(if i.val < 5065 then
5116
else
7446)
else
(if i.val < 5067 then
4542
else
7829))
else
(if i.val < 5070 then
(if i.val < 5069 then
2340
else
7737)
else
(if i.val < 5071 then
1076
else
8184))))
else
(if i.val < 5080 then
(if i.val < 5076 then
(if i.val < 5074 then
(if i.val < 5073 then
8307
else
5658)
else
(if i.val < 5075 then
5628
else
5710))
else
(if i.val < 5078 then
(if i.val < 5077 then
4369
else
4476)
else
(if i.val < 5079 then
7466
else
8198)))
else
(if i.val < 5084 then
(if i.val < 5082 then
(if i.val < 5081 then
7739
else
3814)
else
(if i.val < 5083 then
7634
else
7742))
else
(if i.val < 5086 then
(if i.val < 5085 then
7160
else
7740)
else
(if i.val < 5087 then
7156
else
7154)))))
else
(if i.val < 5104 then
(if i.val < 5096 then
(if i.val < 5092 then
(if i.val < 5090 then
(if i.val < 5089 then
2485
else
2185)
else
(if i.val < 5091 then
7011
else
7516))
else
(if i.val < 5094 then
(if i.val < 5093 then
7157
else
7792)
else
(if i.val < 5095 then
6946
else
1320)))
else
(if i.val < 5100 then
(if i.val < 5098 then
(if i.val < 5097 then
7468
else
6997)
else
(if i.val < 5099 then
5399
else
8104))
else
(if i.val < 5102 then
(if i.val < 5101 then
4912
else
7443)
else
(if i.val < 5103 then
6641
else
2285))))
else
(if i.val < 5112 then
(if i.val < 5108 then
(if i.val < 5106 then
(if i.val < 5105 then
7158
else
3531)
else
(if i.val < 5107 then
3340
else
4744))
else
(if i.val < 5110 then
(if i.val < 5109 then
2634
else
5104)
else
(if i.val < 5111 then
3332
else
5295)))
else
(if i.val < 5116 then
(if i.val < 5114 then
(if i.val < 5113 then
2798
else
5171)
else
(if i.val < 5115 then
6322
else
7155))
else
(if i.val < 5118 then
(if i.val < 5117 then
8075
else
4619)
else
(if i.val < 5119 then
8308
else
4812)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0010 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 5376 then
(if i.val < 5248 then
(if i.val < 5184 then
(if i.val < 5152 then
(if i.val < 5136 then
(if i.val < 5128 then
(if i.val < 5124 then
(if i.val < 5122 then
(if i.val < 5121 then
7498
else
2270)
else
(if i.val < 5123 then
3341
else
5309))
else
(if i.val < 5126 then
(if i.val < 5125 then
8309
else
7970)
else
(if i.val < 5127 then
4522
else
1209)))
else
(if i.val < 5132 then
(if i.val < 5130 then
(if i.val < 5129 then
1210
else
1211)
else
(if i.val < 5131 then
3112
else
6832))
else
(if i.val < 5134 then
(if i.val < 5133 then
7402
else
7342)
else
(if i.val < 5135 then
5572
else
4436))))
else
(if i.val < 5144 then
(if i.val < 5140 then
(if i.val < 5138 then
(if i.val < 5137 then
7345
else
1634)
else
(if i.val < 5139 then
3311
else
7343))
else
(if i.val < 5142 then
(if i.val < 5141 then
7344
else
1061)
else
(if i.val < 5143 then
1276
else
1497)))
else
(if i.val < 5148 then
(if i.val < 5146 then
(if i.val < 5145 then
2926
else
4065)
else
(if i.val < 5147 then
1507
else
3229))
else
(if i.val < 5150 then
(if i.val < 5149 then
3148
else
1517)
else
(if i.val < 5151 then
3144
else
3189)))))
else
(if i.val < 5168 then
(if i.val < 5160 then
(if i.val < 5156 then
(if i.val < 5154 then
(if i.val < 5153 then
3909
else
3834)
else
(if i.val < 5155 then
6374
else
2494))
else
(if i.val < 5158 then
(if i.val < 5157 then
2742
else
7735)
else
(if i.val < 5159 then
7736
else
4804)))
else
(if i.val < 5164 then
(if i.val < 5162 then
(if i.val < 5161 then
7097
else
7738)
else
(if i.val < 5163 then
5204
else
2713))
else
(if i.val < 5166 then
(if i.val < 5165 then
1012
else
6950)
else
(if i.val < 5167 then
5187
else
6951))))
else
(if i.val < 5176 then
(if i.val < 5172 then
(if i.val < 5170 then
(if i.val < 5169 then
2803
else
6952)
else
(if i.val < 5171 then
2812
else
6953))
else
(if i.val < 5174 then
(if i.val < 5173 then
2544
else
1143)
else
(if i.val < 5175 then
7013
else
7014)))
else
(if i.val < 5180 then
(if i.val < 5178 then
(if i.val < 5177 then
2488
else
7015)
else
(if i.val < 5179 then
2751
else
5610))
else
(if i.val < 5182 then
(if i.val < 5181 then
7017
else
7018)
else
(if i.val < 5183 then
7019
else
7020))))))
else
(if i.val < 5216 then
(if i.val < 5200 then
(if i.val < 5192 then
(if i.val < 5188 then
(if i.val < 5186 then
(if i.val < 5185 then
3056
else
7150)
else
(if i.val < 5187 then
1286
else
7151))
else
(if i.val < 5190 then
(if i.val < 5189 then
5700
else
8128)
else
(if i.val < 5191 then
8310
else
5325)))
else
(if i.val < 5196 then
(if i.val < 5194 then
(if i.val < 5193 then
3540
else
2807)
else
(if i.val < 5195 then
1870
else
1291))
else
(if i.val < 5198 then
(if i.val < 5197 then
7420
else
1218)
else
(if i.val < 5199 then
7162
else
3589))))
else
(if i.val < 5208 then
(if i.val < 5204 then
(if i.val < 5202 then
(if i.val < 5201 then
7554
else
2930)
else
(if i.val < 5203 then
3322
else
5705))
else
(if i.val < 5206 then
(if i.val < 5205 then
3588
else
3146)
else
(if i.val < 5207 then
7553
else
7555)))
else
(if i.val < 5212 then
(if i.val < 5210 then
(if i.val < 5209 then
3594
else
6104)
else
(if i.val < 5211 then
4726
else
3590))
else
(if i.val < 5214 then
(if i.val < 5213 then
5698
else
7301)
else
(if i.val < 5215 then
8311
else
2408)))))
else
(if i.val < 5232 then
(if i.val < 5224 then
(if i.val < 5220 then
(if i.val < 5218 then
(if i.val < 5217 then
8312
else
6908)
else
(if i.val < 5219 then
7566
else
8313))
else
(if i.val < 5222 then
(if i.val < 5221 then
7311
else
5353)
else
(if i.val < 5223 then
5846
else
8314)))
else
(if i.val < 5228 then
(if i.val < 5226 then
(if i.val < 5225 then
7822
else
5873)
else
(if i.val < 5227 then
7989
else
1719))
else
(if i.val < 5230 then
(if i.val < 5229 then
5877
else
7990)
else
(if i.val < 5231 then
7573
else
7585))))
else
(if i.val < 5240 then
(if i.val < 5236 then
(if i.val < 5234 then
(if i.val < 5233 then
8212
else
6132)
else
(if i.val < 5235 then
6918
else
7879))
else
(if i.val < 5238 then
(if i.val < 5237 then
6615
else
3414)
else
(if i.val < 5239 then
7523
else
5525)))
else
(if i.val < 5244 then
(if i.val < 5242 then
(if i.val < 5241 then
8315
else
8316)
else
(if i.val < 5243 then
3072
else
7512))
else
(if i.val < 5246 then
(if i.val < 5245 then
3096
else
6093)
else
(if i.val < 5247 then
7429
else
7040)))))))
else
(if i.val < 5312 then
(if i.val < 5280 then
(if i.val < 5264 then
(if i.val < 5256 then
(if i.val < 5252 then
(if i.val < 5250 then
(if i.val < 5249 then
7055
else
4043)
else
(if i.val < 5251 then
7054
else
7165))
else
(if i.val < 5254 then
(if i.val < 5253 then
7753
else
8264)
else
(if i.val < 5255 then
5917
else
7455)))
else
(if i.val < 5260 then
(if i.val < 5258 then
(if i.val < 5257 then
2401
else
6960)
else
(if i.val < 5259 then
4567
else
7518))
else
(if i.val < 5262 then
(if i.val < 5261 then
3893
else
3192)
else
(if i.val < 5263 then
1335
else
2716))))
else
(if i.val < 5272 then
(if i.val < 5268 then
(if i.val < 5266 then
(if i.val < 5265 then
1713
else
3138)
else
(if i.val < 5267 then
7164
else
5763))
else
(if i.val < 5270 then
(if i.val < 5269 then
8200
else
8162)
else
(if i.val < 5271 then
7089
else
6912)))
else
(if i.val < 5276 then
(if i.val < 5274 then
(if i.val < 5273 then
8041
else
2553)
else
(if i.val < 5275 then
8317
else
8318))
else
(if i.val < 5278 then
(if i.val < 5277 then
7932
else
7170)
else
(if i.val < 5279 then
6879
else
5747)))))
else
(if i.val < 5296 then
(if i.val < 5288 then
(if i.val < 5284 then
(if i.val < 5282 then
(if i.val < 5281 then
8319
else
4046)
else
(if i.val < 5283 then
8320
else
7519))
else
(if i.val < 5286 then
(if i.val < 5285 then
3915
else
2880)
else
(if i.val < 5287 then
5552
else
5883)))
else
(if i.val < 5292 then
(if i.val < 5290 then
(if i.val < 5289 then
2639
else
6372)
else
(if i.val < 5291 then
7439
else
2216))
else
(if i.val < 5294 then
(if i.val < 5293 then
8058
else
5731)
else
(if i.val < 5295 then
7754
else
7490))))
else
(if i.val < 5304 then
(if i.val < 5300 then
(if i.val < 5298 then
(if i.val < 5297 then
4063
else
3852)
else
(if i.val < 5299 then
7624
else
3428))
else
(if i.val < 5302 then
(if i.val < 5301 then
5976
else
7628)
else
(if i.val < 5303 then
8201
else
7383)))
else
(if i.val < 5308 then
(if i.val < 5306 then
(if i.val < 5305 then
6381
else
5002)
else
(if i.val < 5307 then
1427
else
1363))
else
(if i.val < 5310 then
(if i.val < 5309 then
7580
else
8257)
else
(if i.val < 5311 then
6152
else
6328))))))
else
(if i.val < 5344 then
(if i.val < 5328 then
(if i.val < 5320 then
(if i.val < 5316 then
(if i.val < 5314 then
(if i.val < 5313 then
7637
else
7758)
else
(if i.val < 5315 then
1348
else
7759))
else
(if i.val < 5318 then
(if i.val < 5317 then
7063
else
5296)
else
(if i.val < 5319 then
1356
else
7640)))
else
(if i.val < 5324 then
(if i.val < 5322 then
(if i.val < 5321 then
7760
else
7592)
else
(if i.val < 5323 then
5163
else
1844))
else
(if i.val < 5326 then
(if i.val < 5325 then
7172
else
4679)
else
(if i.val < 5327 then
7707
else
8321))))
else
(if i.val < 5336 then
(if i.val < 5332 then
(if i.val < 5330 then
(if i.val < 5329 then
7756
else
1432)
else
(if i.val < 5331 then
3337
else
5242))
else
(if i.val < 5334 then
(if i.val < 5333 then
5514
else
7326)
else
(if i.val < 5335 then
6883
else
4844)))
else
(if i.val < 5340 then
(if i.val < 5338 then
(if i.val < 5337 then
3539
else
1424)
else
(if i.val < 5339 then
6943
else
3151))
else
(if i.val < 5342 then
(if i.val < 5341 then
7641
else
1345)
else
(if i.val < 5343 then
4719
else
8247)))))
else
(if i.val < 5360 then
(if i.val < 5352 then
(if i.val < 5348 then
(if i.val < 5346 then
(if i.val < 5345 then
7095
else
7451)
else
(if i.val < 5347 then
8270
else
7079))
else
(if i.val < 5350 then
(if i.val < 5349 then
7674
else
8272)
else
(if i.val < 5351 then
4940
else
5912)))
else
(if i.val < 5356 then
(if i.val < 5354 then
(if i.val < 5353 then
1937
else
7073)
else
(if i.val < 5355 then
7669
else
6170))
else
(if i.val < 5358 then
(if i.val < 5357 then
8025
else
7428)
else
(if i.val < 5359 then
7417
else
7430))))
else
(if i.val < 5368 then
(if i.val < 5364 then
(if i.val < 5362 then
(if i.val < 5361 then
2960
else
2196)
else
(if i.val < 5363 then
4006
else
5562))
else
(if i.val < 5366 then
(if i.val < 5365 then
3058
else
1362)
else
(if i.val < 5367 then
1359
else
5849)))
else
(if i.val < 5372 then
(if i.val < 5370 then
(if i.val < 5369 then
3813
else
3529)
else
(if i.val < 5371 then
1081
else
1077))
else
(if i.val < 5374 then
(if i.val < 5373 then
1355
else
1365)
else
(if i.val < 5375 then
6985
else
2712))))))))
else
(if i.val < 5504 then
(if i.val < 5440 then
(if i.val < 5408 then
(if i.val < 5392 then
(if i.val < 5384 then
(if i.val < 5380 then
(if i.val < 5378 then
(if i.val < 5377 then
7042
else
7749)
else
(if i.val < 5379 then
1369
else
3331))
else
(if i.val < 5382 then
(if i.val < 5381 then
4580
else
1084)
else
(if i.val < 5383 then
3161
else
3158)))
else
(if i.val < 5388 then
(if i.val < 5386 then
(if i.val < 5385 then
3253
else
3164)
else
(if i.val < 5387 then
3777
else
1949))
else
(if i.val < 5390 then
(if i.val < 5389 then
7688
else
7171)
else
(if i.val < 5391 then
3798
else
7768))))
else
(if i.val < 5400 then
(if i.val < 5396 then
(if i.val < 5394 then
(if i.val < 5393 then
8187
else
3778)
else
(if i.val < 5395 then
4869
else
5842))
else
(if i.val < 5398 then
(if i.val < 5397 then
7142
else
1114)
else
(if i.val < 5399 then
8322
else
8220)))
else
(if i.val < 5404 then
(if i.val < 5402 then
(if i.val < 5401 then
7169
else
3338)
else
(if i.val < 5403 then
5659
else
1212))
else
(if i.val < 5406 then
(if i.val < 5405 then
1213
else
1203)
else
(if i.val < 5407 then
1214
else
1215)))))
else
(if i.val < 5424 then
(if i.val < 5416 then
(if i.val < 5412 then
(if i.val < 5410 then
(if i.val < 5409 then
1202
else
1204)
else
(if i.val < 5411 then
1198
else
1280))
else
(if i.val < 5414 then
(if i.val < 5413 then
1249
else
1255)
else
(if i.val < 5415 then
1258
else
1247)))
else
(if i.val < 5420 then
(if i.val < 5418 then
(if i.val < 5417 then
1282
else
1289)
else
(if i.val < 5419 then
1423
else
1426))
else
(if i.val < 5422 then
(if i.val < 5421 then
1428
else
1371)
else
(if i.val < 5423 then
1368
else
1429))))
else
(if i.val < 5432 then
(if i.val < 5428 then
(if i.val < 5426 then
(if i.val < 5425 then
1430
else
1433)
else
(if i.val < 5427 then
1434
else
1435))
else
(if i.val < 5430 then
(if i.val < 5429 then
1436
else
1350)
else
(if i.val < 5431 then
1372
else
1349)))
else
(if i.val < 5436 then
(if i.val < 5434 then
(if i.val < 5433 then
1450
else
1452)
else
(if i.val < 5435 then
1453
else
1454))
else
(if i.val < 5438 then
(if i.val < 5437 then
1455
else
1382)
else
(if i.val < 5439 then
1378
else
7501))))))
else
(if i.val < 5472 then
(if i.val < 5456 then
(if i.val < 5448 then
(if i.val < 5444 then
(if i.val < 5442 then
(if i.val < 5441 then
7503
else
7505)
else
(if i.val < 5443 then
7506
else
4895))
else
(if i.val < 5446 then
(if i.val < 5445 then
7229
else
7550)
else
(if i.val < 5447 then
6471
else
7710)))
else
(if i.val < 5452 then
(if i.val < 5450 then
(if i.val < 5449 then
7711
else
7618)
else
(if i.val < 5451 then
5288
else
6154))
else
(if i.val < 5454 then
(if i.val < 5453 then
7651
else
1467)
else
(if i.val < 5455 then
3134
else
4540))))
else
(if i.val < 5464 then
(if i.val < 5460 then
(if i.val < 5458 then
(if i.val < 5457 then
1472
else
1698)
else
(if i.val < 5459 then
6435
else
1179))
else
(if i.val < 5462 then
(if i.val < 5461 then
5702
else
5625)
else
(if i.val < 5463 then
3218
else
1749)))
else
(if i.val < 5468 then
(if i.val < 5466 then
(if i.val < 5465 then
3132
else
1688)
else
(if i.val < 5467 then
7352
else
1471))
else
(if i.val < 5470 then
(if i.val < 5469 then
1775
else
7714)
else
(if i.val < 5471 then
4304
else
7716)))))
else
(if i.val < 5488 then
(if i.val < 5480 then
(if i.val < 5476 then
(if i.val < 5474 then
(if i.val < 5473 then
2356
else
6976)
else
(if i.val < 5475 then
5184
else
7321))
else
(if i.val < 5478 then
(if i.val < 5477 then
7717
else
7718)
else
(if i.val < 5479 then
3455
else
7323)))
else
(if i.val < 5484 then
(if i.val < 5482 then
(if i.val < 5481 then
2760
else
4518)
else
(if i.val < 5483 then
2955
else
7667))
else
(if i.val < 5486 then
(if i.val < 5485 then
7291
else
3936)
else
(if i.val < 5487 then
2918
else
6001))))
else
(if i.val < 5496 then
(if i.val < 5492 then
(if i.val < 5490 then
(if i.val < 5489 then
1924
else
6851)
else
(if i.val < 5491 then
5971
else
7720))
else
(if i.val < 5494 then
(if i.val < 5493 then
7368
else
4873)
else
(if i.val < 5495 then
5998
else
5057)))
else
(if i.val < 5500 then
(if i.val < 5498 then
(if i.val < 5497 then
6557
else
7654)
else
(if i.val < 5499 then
7725
else
7689))
else
(if i.val < 5502 then
(if i.val < 5501 then
5757
else
5633)
else
(if i.val < 5503 then
7221
else
5060)))))))
else
(if i.val < 5568 then
(if i.val < 5536 then
(if i.val < 5520 then
(if i.val < 5512 then
(if i.val < 5508 then
(if i.val < 5506 then
(if i.val < 5505 then
5587
else
7743)
else
(if i.val < 5507 then
7744
else
7746))
else
(if i.val < 5510 then
(if i.val < 5509 then
5339
else
7747)
else
(if i.val < 5511 then
7748
else
7750)))
else
(if i.val < 5516 then
(if i.val < 5514 then
(if i.val < 5513 then
7751
else
7752)
else
(if i.val < 5515 then
4816
else
7755))
else
(if i.val < 5518 then
(if i.val < 5517 then
6373
else
7072)
else
(if i.val < 5519 then
5520
else
5328))))
else
(if i.val < 5528 then
(if i.val < 5524 then
(if i.val < 5522 then
(if i.val < 5521 then
3913
else
6852)
else
(if i.val < 5523 then
7086
else
2629))
else
(if i.val < 5526 then
(if i.val < 5525 then
7678
else
7038)
else
(if i.val < 5527 then
7494
else
7648)))
else
(if i.val < 5532 then
(if i.val < 5530 then
(if i.val < 5529 then
7757
else
1107)
else
(if i.val < 5531 then
1060
else
1073))
else
(if i.val < 5534 then
(if i.val < 5533 then
1111
else
1074)
else
(if i.val < 5535 then
7009
else
7010)))))
else
(if i.val < 5552 then
(if i.val < 5544 then
(if i.val < 5540 then
(if i.val < 5538 then
(if i.val < 5537 then
4373
else
7130)
else
(if i.val < 5539 then
6476
else
7131))
else
(if i.val < 5542 then
(if i.val < 5541 then
1224
else
2679)
else
(if i.val < 5543 then
4751
else
7134)))
else
(if i.val < 5548 then
(if i.val < 5546 then
(if i.val < 5545 then
4803
else
7135)
else
(if i.val < 5547 then
2519
else
4789))
else
(if i.val < 5550 then
(if i.val < 5549 then
7136
else
5631)
else
(if i.val < 5551 then
5634
else
5635))))
else
(if i.val < 5560 then
(if i.val < 5556 then
(if i.val < 5554 then
(if i.val < 5553 then
7138
else
7139)
else
(if i.val < 5555 then
7101
else
6431))
else
(if i.val < 5558 then
(if i.val < 5557 then
7105
else
7145)
else
(if i.val < 5559 then
7161
else
5548)))
else
(if i.val < 5564 then
(if i.val < 5562 then
(if i.val < 5561 then
7163
else
4606)
else
(if i.val < 5563 then
2943
else
7167))
else
(if i.val < 5566 then
(if i.val < 5565 then
7168
else
4591)
else
(if i.val < 5567 then
3610
else
5090))))))
else
(if i.val < 5600 then
(if i.val < 5584 then
(if i.val < 5576 then
(if i.val < 5572 then
(if i.val < 5570 then
(if i.val < 5569 then
5695
else
1125)
else
(if i.val < 5571 then
6353
else
8136))
else
(if i.val < 5574 then
(if i.val < 5573 then
5584
else
2481)
else
(if i.val < 5575 then
4296
else
8037)))
else
(if i.val < 5580 then
(if i.val < 5578 then
(if i.val < 5577 then
5580
else
6119)
else
(if i.val < 5579 then
3117
else
5879))
else
(if i.val < 5582 then
(if i.val < 5581 then
8137
else
6398)
else
(if i.val < 5583 then
2345
else
5165))))
else
(if i.val < 5592 then
(if i.val < 5588 then
(if i.val < 5586 then
(if i.val < 5585 then
5134
else
5541)
else
(if i.val < 5587 then
7526
else
7812))
else
(if i.val < 5590 then
(if i.val < 5589 then
7856
else
7087)
else
(if i.val < 5591 then
6861
else
5599)))
else
(if i.val < 5596 then
(if i.val < 5594 then
(if i.val < 5593 then
5133
else
8138)
else
(if i.val < 5595 then
6924
else
1139))
else
(if i.val < 5598 then
(if i.val < 5597 then
5752
else
7820)
else
(if i.val < 5599 then
3227
else
2575)))))
else
(if i.val < 5616 then
(if i.val < 5608 then
(if i.val < 5604 then
(if i.val < 5602 then
(if i.val < 5601 then
2474
else
8139)
else
(if i.val < 5603 then
3212
else
7253))
else
(if i.val < 5606 then
(if i.val < 5605 then
1303
else
7698)
else
(if i.val < 5607 then
8140
else
8141)))
else
(if i.val < 5612 then
(if i.val < 5610 then
(if i.val < 5609 then
7763
else
7297)
else
(if i.val < 5611 then
8142
else
1306))
else
(if i.val < 5614 then
(if i.val < 5613 then
2317
else
7625)
else
(if i.val < 5615 then
5299
else
8112))))
else
(if i.val < 5624 then
(if i.val < 5620 then
(if i.val < 5618 then
(if i.val < 5617 then
5810
else
4573)
else
(if i.val < 5619 then
2502
else
2868))
else
(if i.val < 5622 then
(if i.val < 5621 then
8143
else
2858)
else
(if i.val < 5623 then
2321
else
1906)))
else
(if i.val < 5628 then
(if i.val < 5626 then
(if i.val < 5625 then
8144
else
2735)
else
(if i.val < 5627 then
8146
else
7660))
else
(if i.val < 5630 then
(if i.val < 5629 then
2856
else
7858)
else
(if i.val < 5631 then
7841
else
4985)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0011 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 5888 then
(if i.val < 5760 then
(if i.val < 5696 then
(if i.val < 5664 then
(if i.val < 5648 then
(if i.val < 5640 then
(if i.val < 5636 then
(if i.val < 5634 then
(if i.val < 5633 then
3374
else
7840)
else
(if i.val < 5635 then
7521
else
6187))
else
(if i.val < 5638 then
(if i.val < 5637 then
8147
else
4770)
else
(if i.val < 5639 then
3786
else
2965)))
else
(if i.val < 5644 then
(if i.val < 5642 then
(if i.val < 5641 then
6390
else
7847)
else
(if i.val < 5643 then
7570
else
7324))
else
(if i.val < 5646 then
(if i.val < 5645 then
4724
else
7034)
else
(if i.val < 5647 then
1563
else
1564))))
else
(if i.val < 5656 then
(if i.val < 5652 then
(if i.val < 5650 then
(if i.val < 5649 then
2399
else
7128)
else
(if i.val < 5651 then
5675
else
4614))
else
(if i.val < 5654 then
(if i.val < 5653 then
7913
else
7914)
else
(if i.val < 5655 then
7788
else
1845)))
else
(if i.val < 5660 then
(if i.val < 5658 then
(if i.val < 5657 then
6099
else
6360)
else
(if i.val < 5659 then
8149
else
8150))
else
(if i.val < 5662 then
(if i.val < 5661 then
7419
else
1495)
else
(if i.val < 5663 then
1496
else
1484)))))
else
(if i.val < 5680 then
(if i.val < 5672 then
(if i.val < 5668 then
(if i.val < 5666 then
(if i.val < 5665 then
4733
else
6848)
else
(if i.val < 5667 then
4768
else
7077))
else
(if i.val < 5670 then
(if i.val < 5669 then
7855
else
1849)
else
(if i.val < 5671 then
4754
else
4314)))
else
(if i.val < 5676 then
(if i.val < 5674 then
(if i.val < 5673 then
6630
else
7857)
else
(if i.val < 5675 then
6535
else
2554))
else
(if i.val < 5678 then
(if i.val < 5677 then
4901
else
2906)
else
(if i.val < 5679 then
4468
else
7107))))
else
(if i.val < 5688 then
(if i.val < 5684 then
(if i.val < 5682 then
(if i.val < 5681 then
6426
else
8159)
else
(if i.val < 5683 then
8160
else
3783))
else
(if i.val < 5686 then
(if i.val < 5685 then
4576
else
2297)
else
(if i.val < 5687 then
5223
else
4625)))
else
(if i.val < 5692 then
(if i.val < 5690 then
(if i.val < 5689 then
5241
else
2338)
else
(if i.val < 5691 then
5072
else
4473))
else
(if i.val < 5694 then
(if i.val < 5693 then
4813
else
6462)
else
(if i.val < 5695 then
5517
else
7275))))))
else
(if i.val < 5728 then
(if i.val < 5712 then
(if i.val < 5704 then
(if i.val < 5700 then
(if i.val < 5698 then
(if i.val < 5697 then
3849
else
2291)
else
(if i.val < 5699 then
7358
else
7563))
else
(if i.val < 5702 then
(if i.val < 5701 then
8161
else
7021)
else
(if i.val < 5703 then
2696
else
2756)))
else
(if i.val < 5708 then
(if i.val < 5706 then
(if i.val < 5705 then
8163
else
2896)
else
(if i.val < 5707 then
1319
else
5266))
else
(if i.val < 5710 then
(if i.val < 5709 then
2881
else
3413)
else
(if i.val < 5711 then
6423
else
1322))))
else
(if i.val < 5720 then
(if i.val < 5716 then
(if i.val < 5714 then
(if i.val < 5713 then
4501
else
7920)
else
(if i.val < 5715 then
2878
else
3931))
else
(if i.val < 5718 then
(if i.val < 5717 then
2879
else
2357)
else
(if i.val < 5719 then
1989
else
4361)))
else
(if i.val < 5724 then
(if i.val < 5722 then
(if i.val < 5721 then
6928
else
5278)
else
(if i.val < 5723 then
6429
else
8164))
else
(if i.val < 5726 then
(if i.val < 5725 then
4415
else
7921)
else
(if i.val < 5727 then
2320
else
7887)))))
else
(if i.val < 5744 then
(if i.val < 5736 then
(if i.val < 5732 then
(if i.val < 5730 then
(if i.val < 5729 then
2256
else
7922)
else
(if i.val < 5731 then
7851
else
6504))
else
(if i.val < 5734 then
(if i.val < 5733 then
5815
else
2757)
else
(if i.val < 5735 then
6874
else
2264)))
else
(if i.val < 5740 then
(if i.val < 5738 then
(if i.val < 5737 then
6438
else
3923)
else
(if i.val < 5739 then
8106
else
4623))
else
(if i.val < 5742 then
(if i.val < 5741 then
6362
else
8117)
else
(if i.val < 5743 then
5392
else
2937))))
else
(if i.val < 5752 then
(if i.val < 5748 then
(if i.val < 5746 then
(if i.val < 5745 then
2688
else
4404)
else
(if i.val < 5747 then
7478
else
7897))
else
(if i.val < 5750 then
(if i.val < 5749 then
6944
else
2877)
else
(if i.val < 5751 then
1531
else
1532)))
else
(if i.val < 5756 then
(if i.val < 5754 then
(if i.val < 5753 then
2529
else
6837)
else
(if i.val < 5755 then
5724
else
1534))
else
(if i.val < 5758 then
(if i.val < 5757 then
7632
else
3330)
else
(if i.val < 5759 then
7659
else
5516)))))))
else
(if i.val < 5824 then
(if i.val < 5792 then
(if i.val < 5776 then
(if i.val < 5768 then
(if i.val < 5764 then
(if i.val < 5762 then
(if i.val < 5761 then
3887
else
5393)
else
(if i.val < 5763 then
3806
else
8165))
else
(if i.val < 5766 then
(if i.val < 5765 then
4427
else
4587)
else
(if i.val < 5767 then
6148
else
5388)))
else
(if i.val < 5772 then
(if i.val < 5770 then
(if i.val < 5769 then
2449
else
996)
else
(if i.val < 5771 then
997
else
992))
else
(if i.val < 5774 then
(if i.val < 5773 then
1165
else
1166)
else
(if i.val < 5775 then
1156
else
1150))))
else
(if i.val < 5784 then
(if i.val < 5780 then
(if i.val < 5778 then
(if i.val < 5777 then
1171
else
1556)
else
(if i.val < 5779 then
1558
else
1523))
else
(if i.val < 5782 then
(if i.val < 5781 then
1560
else
1536)
else
(if i.val < 5783 then
1524
else
1566)))
else
(if i.val < 5788 then
(if i.val < 5786 then
(if i.val < 5785 then
1568
else
7278)
else
(if i.val < 5787 then
7279
else
7102))
else
(if i.val < 5790 then
(if i.val < 5789 then
7906
else
7907)
else
(if i.val < 5791 then
7908
else
6114)))))
else
(if i.val < 5808 then
(if i.val < 5800 then
(if i.val < 5796 then
(if i.val < 5794 then
(if i.val < 5793 then
4741
else
5850)
else
(if i.val < 5795 then
5884
else
7909))
else
(if i.val < 5798 then
(if i.val < 5797 then
7529
else
7910)
else
(if i.val < 5799 then
7881
else
3296)))
else
(if i.val < 5804 then
(if i.val < 5802 then
(if i.val < 5801 then
7528
else
4558)
else
(if i.val < 5803 then
4452
else
7911))
else
(if i.val < 5806 then
(if i.val < 5805 then
4297
else
7461)
else
(if i.val < 5807 then
7912
else
3166))))
else
(if i.val < 5816 then
(if i.val < 5812 then
(if i.val < 5810 then
(if i.val < 5809 then
7779
else
5380)
else
(if i.val < 5811 then
6990
else
2403))
else
(if i.val < 5814 then
(if i.val < 5813 then
5213
else
7187)
else
(if i.val < 5815 then
7919
else
7070)))
else
(if i.val < 5820 then
(if i.val < 5818 then
(if i.val < 5817 then
5210
else
6432)
else
(if i.val < 5819 then
6437
else
4410))
else
(if i.val < 5822 then
(if i.val < 5821 then
7893
else
7312)
else
(if i.val < 5823 then
1492
else
1478))))))
else
(if i.val < 5856 then
(if i.val < 5840 then
(if i.val < 5832 then
(if i.val < 5828 then
(if i.val < 5826 then
(if i.val < 5825 then
7814
else
1133)
else
(if i.val < 5827 then
5025
else
1222))
else
(if i.val < 5830 then
(if i.val < 5829 then
5062
else
4747)
else
(if i.val < 5831 then
2680
else
4611)))
else
(if i.val < 5836 then
(if i.val < 5834 then
(if i.val < 5833 then
4682
else
6975)
else
(if i.val < 5835 then
7849
else
3989))
else
(if i.val < 5838 then
(if i.val < 5837 then
2453
else
4814)
else
(if i.val < 5839 then
8035
else
7454))))
else
(if i.val < 5848 then
(if i.val < 5844 then
(if i.val < 5842 then
(if i.val < 5841 then
2568
else
7819)
else
(if i.val < 5843 then
6122
else
6447))
else
(if i.val < 5846 then
(if i.val < 5845 then
5258
else
2935)
else
(if i.val < 5847 then
3129
else
3886)))
else
(if i.val < 5852 then
(if i.val < 5850 then
(if i.val < 5849 then
5139
else
7896)
else
(if i.val < 5851 then
2538
else
4833))
else
(if i.val < 5854 then
(if i.val < 5853 then
5183
else
7083)
else
(if i.val < 5855 then
6470
else
5019)))))
else
(if i.val < 5872 then
(if i.val < 5864 then
(if i.val < 5860 then
(if i.val < 5858 then
(if i.val < 5857 then
1610
else
7842)
else
(if i.val < 5859 then
7980
else
7979))
else
(if i.val < 5862 then
(if i.val < 5861 then
4832
else
6422)
else
(if i.val < 5863 then
5106
else
5122)))
else
(if i.val < 5868 then
(if i.val < 5866 then
(if i.val < 5865 then
5110
else
3375)
else
(if i.val < 5867 then
4849
else
3121))
else
(if i.val < 5870 then
(if i.val < 5869 then
7103
else
1333)
else
(if i.val < 5871 then
3845
else
4010))))
else
(if i.val < 5880 then
(if i.val < 5876 then
(if i.val < 5874 then
(if i.val < 5873 then
5302
else
7333)
else
(if i.val < 5875 then
5693
else
5689))
else
(if i.val < 5878 then
(if i.val < 5877 then
8039
else
7367)
else
(if i.val < 5879 then
5582
else
7962)))
else
(if i.val < 5884 then
(if i.val < 5882 then
(if i.val < 5881 then
5327
else
8040)
else
(if i.val < 5883 then
5714
else
2520))
else
(if i.val < 5886 then
(if i.val < 5885 then
2546
else
2754)
else
(if i.val < 5887 then
5245
else
3130))))))))
else
(if i.val < 6016 then
(if i.val < 5952 then
(if i.val < 5920 then
(if i.val < 5904 then
(if i.val < 5896 then
(if i.val < 5892 then
(if i.val < 5890 then
(if i.val < 5889 then
6109
else
1910)
else
(if i.val < 5891 then
1377
else
5261))
else
(if i.val < 5894 then
(if i.val < 5893 then
5589
else
1716)
else
(if i.val < 5895 then
8043
else
5938)))
else
(if i.val < 5900 then
(if i.val < 5898 then
(if i.val < 5897 then
2846
else
3929)
else
(if i.val < 5899 then
7987
else
2239))
else
(if i.val < 5902 then
(if i.val < 5901 then
2600
else
7650)
else
(if i.val < 5903 then
7988
else
7894))))
else
(if i.val < 5912 then
(if i.val < 5908 then
(if i.val < 5906 then
(if i.val < 5905 then
7339
else
5762)
else
(if i.val < 5907 then
7672
else
3612))
else
(if i.val < 5910 then
(if i.val < 5909 then
4909
else
7972)
else
(if i.val < 5911 then
6921
else
2236)))
else
(if i.val < 5916 then
(if i.val < 5914 then
(if i.val < 5913 then
2552
else
8044)
else
(if i.val < 5915 then
4686
else
3178))
else
(if i.val < 5918 then
(if i.val < 5917 then
5760
else
8045)
else
(if i.val < 5919 then
1126
else
1137)))))
else
(if i.val < 5936 then
(if i.val < 5928 then
(if i.val < 5924 then
(if i.val < 5922 then
(if i.val < 5921 then
1606
else
1607)
else
(if i.val < 5923 then
1597
else
1608))
else
(if i.val < 5926 then
(if i.val < 5925 then
1598
else
1592)
else
(if i.val < 5927 then
1611
else
7977)))
else
(if i.val < 5932 then
(if i.val < 5930 then
(if i.val < 5929 then
7978
else
1868)
else
(if i.val < 5931 then
4560
else
1888))
else
(if i.val < 5934 then
(if i.val < 5933 then
7349
else
4899)
else
(if i.val < 5935 then
4377
else
6966))))
else
(if i.val < 5944 then
(if i.val < 5940 then
(if i.val < 5938 then
(if i.val < 5937 then
2240
else
6451)
else
(if i.val < 5939 then
7346
else
5900))
else
(if i.val < 5942 then
(if i.val < 5941 then
5679
else
6100)
else
(if i.val < 5943 then
4905
else
6116)))
else
(if i.val < 5948 then
(if i.val < 5946 then
(if i.val < 5945 then
7510
else
5046)
else
(if i.val < 5947 then
7986
else
4775))
else
(if i.val < 5950 then
(if i.val < 5949 then
2540
else
4592)
else
(if i.val < 5951 then
6876
else
1326))))))
else
(if i.val < 5984 then
(if i.val < 5968 then
(if i.val < 5960 then
(if i.val < 5956 then
(if i.val < 5954 then
(if i.val < 5953 then
7603
else
6964)
else
(if i.val < 5955 then
5107
else
2273))
else
(if i.val < 5958 then
(if i.val < 5957 then
5581
else
6118)
else
(if i.val < 5959 then
1874
else
3812)))
else
(if i.val < 5964 then
(if i.val < 5962 then
(if i.val < 5961 then
7289
else
7288)
else
(if i.val < 5963 then
3195
else
3135))
else
(if i.val < 5966 then
(if i.val < 5965 then
3549
else
2359)
else
(if i.val < 5967 then
1338
else
6407))))
else
(if i.val < 5976 then
(if i.val < 5972 then
(if i.val < 5970 then
(if i.val < 5969 then
3094
else
1027)
else
(if i.val < 5971 then
8018
else
2923))
else
(if i.val < 5974 then
(if i.val < 5973 then
8004
else
5764)
else
(if i.val < 5975 then
6448
else
8012)))
else
(if i.val < 5980 then
(if i.val < 5978 then
(if i.val < 5977 then
3895
else
3894)
else
(if i.val < 5979 then
8046
else
6113))
else
(if i.val < 5982 then
(if i.val < 5981 then
4547
else
5613)
else
(if i.val < 5983 then
5359
else
8047)))))
else
(if i.val < 6000 then
(if i.val < 5992 then
(if i.val < 5988 then
(if i.val < 5986 then
(if i.val < 5985 then
5974
else
1479)
else
(if i.val < 5987 then
7023
else
6139))
else
(if i.val < 5990 then
(if i.val < 5989 then
6456
else
6500)
else
(if i.val < 5991 then
7260
else
4537)))
else
(if i.val < 5996 then
(if i.val < 5994 then
(if i.val < 5993 then
1655
else
7267)
else
(if i.val < 5995 then
7380
else
2854))
else
(if i.val < 5998 then
(if i.val < 5997 then
4776
else
7655)
else
(if i.val < 5999 then
2900
else
8019))))
else
(if i.val < 6008 then
(if i.val < 6004 then
(if i.val < 6002 then
(if i.val < 6001 then
7212
else
3061)
else
(if i.val < 6003 then
5237
else
7389))
else
(if i.val < 6006 then
(if i.val < 6005 then
7591
else
1595)
else
(if i.val < 6007 then
1594
else
5709)))
else
(if i.val < 6012 then
(if i.val < 6010 then
(if i.val < 6009 then
1622
else
1628)
else
(if i.val < 6011 then
1653
else
6206))
else
(if i.val < 6014 then
(if i.val < 6013 then
4523
else
7265)
else
(if i.val < 6015 then
1149
else
1637)))))))
else
(if i.val < 6080 then
(if i.val < 6048 then
(if i.val < 6032 then
(if i.val < 6024 then
(if i.val < 6020 then
(if i.val < 6018 then
(if i.val < 6017 then
1591
else
6631)
else
(if i.val < 6019 then
5000
else
4970))
else
(if i.val < 6022 then
(if i.val < 6021 then
4870
else
4977)
else
(if i.val < 6023 then
1933
else
5379)))
else
(if i.val < 6028 then
(if i.val < 6026 then
(if i.val < 6025 then
7767
else
5330)
else
(if i.val < 6027 then
5089
else
4293))
else
(if i.val < 6030 then
(if i.val < 6029 then
7831
else
7806)
else
(if i.val < 6031 then
1456
else
7296))))
else
(if i.val < 6040 then
(if i.val < 6036 then
(if i.val < 6034 then
(if i.val < 6033 then
3310
else
5155)
else
(if i.val < 6035 then
7852
else
8048))
else
(if i.val < 6038 then
(if i.val < 6037 then
5618
else
6417)
else
(if i.val < 6039 then
8049
else
1499)))
else
(if i.val < 6044 then
(if i.val < 6042 then
(if i.val < 6041 then
4976
else
8050)
else
(if i.val < 6043 then
5632
else
1240))
else
(if i.val < 6046 then
(if i.val < 6045 then
8051
else
6419)
else
(if i.val < 6047 then
6367
else
5036)))))
else
(if i.val < 6064 then
(if i.val < 6056 then
(if i.val < 6052 then
(if i.val < 6050 then
(if i.val < 6049 then
4808
else
4422)
else
(if i.val < 6051 then
2695
else
8026))
else
(if i.val < 6054 then
(if i.val < 6053 then
1571
else
1573)
else
(if i.val < 6055 then
1576
else
981)))
else
(if i.val < 6060 then
(if i.val < 6058 then
(if i.val < 6057 then
1127
else
1128)
else
(if i.val < 6059 then
1129
else
1130))
else
(if i.val < 6062 then
(if i.val < 6061 then
1131
else
1580)
else
(if i.val < 6063 then
1586
else
1588))))
else
(if i.val < 6072 then
(if i.val < 6068 then
(if i.val < 6066 then
(if i.val < 6065 then
1589
else
1600)
else
(if i.val < 6067 then
7708
else
3430))
else
(if i.val < 6070 then
(if i.val < 6069 then
8009
else
8166)
else
(if i.val < 6071 then
2708
else
7225)))
else
(if i.val < 6076 then
(if i.val < 6074 then
(if i.val < 6073 then
1293
else
2826)
else
(if i.val < 6075 then
7534
else
7700))
else
(if i.val < 6078 then
(if i.val < 6077 then
4577
else
7416)
else
(if i.val < 6079 then
1358
else
8167))))))
else
(if i.val < 6112 then
(if i.val < 6096 then
(if i.val < 6088 then
(if i.val < 6084 then
(if i.val < 6082 then
(if i.val < 6081 then
7578
else
6963)
else
(if i.val < 6083 then
8064
else
8061))
else
(if i.val < 6086 then
(if i.val < 6085 then
3544
else
1928)
else
(if i.val < 6087 then
6082
else
8006)))
else
(if i.val < 6092 then
(if i.val < 6090 then
(if i.val < 6089 then
7522
else
7366)
else
(if i.val < 6091 then
2829
else
7520))
else
(if i.val < 6094 then
(if i.val < 6093 then
2685
else
5886)
else
(if i.val < 6095 then
3433
else
7942))))
else
(if i.val < 6104 then
(if i.val < 6100 then
(if i.val < 6098 then
(if i.val < 6097 then
1058
else
6087)
else
(if i.val < 6099 then
3842
else
3239))
else
(if i.val < 6102 then
(if i.val < 6101 then
3829
else
7247)
else
(if i.val < 6103 then
3364
else
3431)))
else
(if i.val < 6108 then
(if i.val < 6106 then
(if i.val < 6105 then
8052
else
1706)
else
(if i.val < 6107 then
8076
else
3857))
else
(if i.val < 6110 then
(if i.val < 6109 then
7800
else
3920)
else
(if i.val < 6111 then
5524
else
8119)))))
else
(if i.val < 6128 then
(if i.val < 6120 then
(if i.val < 6116 then
(if i.val < 6114 then
(if i.val < 6113 then
3912
else
8054)
else
(if i.val < 6115 then
2570
else
3898))
else
(if i.val < 6118 then
(if i.val < 6117 then
4531
else
5035)
else
(if i.val < 6119 then
7862
else
8083)))
else
(if i.val < 6124 then
(if i.val < 6122 then
(if i.val < 6121 then
2530
else
1717)
else
(if i.val < 6123 then
5395
else
1700))
else
(if i.val < 6126 then
(if i.val < 6125 then
5396
else
6459)
else
(if i.val < 6127 then
1380
else
1243))))
else
(if i.val < 6136 then
(if i.val < 6132 then
(if i.val < 6130 then
(if i.val < 6129 then
3809
else
8096)
else
(if i.val < 6131 then
7671
else
1729))
else
(if i.val < 6134 then
(if i.val < 6133 then
8168
else
6620)
else
(if i.val < 6135 then
7075
else
1981)))
else
(if i.val < 6140 then
(if i.val < 6138 then
(if i.val < 6137 then
5683
else
3636)
else
(if i.val < 6139 then
6070
else
3425))
else
(if i.val < 6142 then
(if i.val < 6141 then
4802
else
7405)
else
(if i.val < 6143 then
4440
else
8169)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_cosetGeneratorNextColumn3Part0012 : Fin 8640 → Fin 8640 :=
  fun i => (if i.val < 6400 then
(if i.val < 6272 then
(if i.val < 6208 then
(if i.val < 6176 then
(if i.val < 6160 then
(if i.val < 6152 then
(if i.val < 6148 then
(if i.val < 6146 then
(if i.val < 6145 then
3597
else
6545)
else
(if i.val < 6147 then
8170
else
1328))
else
(if i.val < 6150 then
(if i.val < 6149 then
8171
else
5190)
else
(if i.val < 6151 then
1329
else
4385)))
else
(if i.val < 6156 then
(if i.val < 6154 then
(if i.val < 6153 then
8100
else
1737)
else
(if i.val < 6155 then
2642
else
3118))
else
(if i.val < 6158 then
(if i.val < 6157 then
5713
else
4712)
else
(if i.val < 6159 then
7609
else
6902))))
else
(if i.val < 6168 then
(if i.val < 6164 then
(if i.val < 6162 then
(if i.val < 6161 then
7766
else
2028)
else
(if i.val < 6163 then
6616
else
5523))
else
(if i.val < 6166 then
(if i.val < 6165 then
1779
else
1776)
else
(if i.val < 6167 then
1520
else
1730)))
else
(if i.val < 6172 then
(if i.val < 6170 then
(if i.val < 6169 then
7207
else
7210)
else
(if i.val < 6171 then
7597
else
6906))
else
(if i.val < 6174 then
(if i.val < 6173 then
1506
else
5385)
else
(if i.val < 6175 then
4569
else
4478)))))
else
(if i.val < 6192 then
(if i.val < 6184 then
(if i.val < 6180 then
(if i.val < 6178 then
(if i.val < 6177 then
6332
else
7090)
else
(if i.val < 6179 then
2373
else
1710))
else
(if i.val < 6182 then
(if i.val < 6181 then
4382
else
4568)
else
(if i.val < 6183 then
4894
else
6897)))
else
(if i.val < 6188 then
(if i.val < 6186 then
(if i.val < 6185 then
1757
else
3990)
else
(if i.val < 6187 then
7248
else
5551))
else
(if i.val < 6190 then
(if i.val < 6189 then
6137
else
8118)
else
(if i.val < 6191 then
1703
else
1689))))
else
(if i.val < 6200 then
(if i.val < 6196 then
(if i.val < 6194 then
(if i.val < 6193 then
1481
else
5383)
else
(if i.val < 6195 then
8120
else
1721))
else
(if i.val < 6198 then
(if i.val < 6197 then
3471
else
1739)
else
(if i.val < 6199 then
2902
else
1741)))
else
(if i.val < 6204 then
(if i.val < 6202 then
(if i.val < 6201 then
7470
else
5386)
else
(if i.val < 6203 then
7471
else
8105))
else
(if i.val < 6206 then
(if i.val < 6205 then
4055
else
1943)
else
(if i.val < 6207 then
8028
else
1732))))))
else
(if i.val < 6240 then
(if i.val < 6224 then
(if i.val < 6216 then
(if i.val < 6212 then
(if i.val < 6210 then
(if i.val < 6209 then
1740
else
1521)
else
(if i.val < 6211 then
7886
else
3665))
else
(if i.val < 6214 then
(if i.val < 6213 then
4349
else
4730)
else
(if i.val < 6215 then
4966
else
7064)))
else
(if i.val < 6220 then
(if i.val < 6218 then
(if i.val < 6217 then
4788
else
2901)
else
(if i.val < 6219 then
5911
else
5004))
else
(if i.val < 6222 then
(if i.val < 6221 then
7246
else
4713)
else
(if i.val < 6223 then
5130
else
4295))))
else
(if i.val < 6232 then
(if i.val < 6228 then
(if i.val < 6226 then
(if i.val < 6225 then
6427
else
1895)
else
(if i.val < 6227 then
5578
else
3105))
else
(if i.val < 6230 then
(if i.val < 6229 then
3423
else
8172)
else
(if i.val < 6231 then
3351
else
7575)))
else
(if i.val < 6236 then
(if i.val < 6234 then
(if i.val < 6233 then
5963
else
8173)
else
(if i.val < 6235 then
5265
else
6396))
else
(if i.val < 6238 then
(if i.val < 6237 then
7931
else
7261)
else
(if i.val < 6239 then
5382
else
8174)))))
else
(if i.val < 6256 then
(if i.val < 6248 then
(if i.val < 6244 then
(if i.val < 6242 then
(if i.val < 6241 then
4785
else
5915)
else
(if i.val < 6243 then
4318
else
2722))
else
(if i.val < 6246 then
(if i.val < 6245 then
5103
else
4451)
else
(if i.val < 6247 then
2284
else
4303)))
else
(if i.val < 6252 then
(if i.val < 6250 then
(if i.val < 6249 then
8175
else
4453)
else
(if i.val < 6251 then
1024
else
6841))
else
(if i.val < 6254 then
(if i.val < 6253 then
7532
else
4856)
else
(if i.val < 6255 then
8176
else
5013))))
else
(if i.val < 6264 then
(if i.val < 6260 then
(if i.val < 6258 then
(if i.val < 6257 then
8115
else
5546)
else
(if i.val < 6259 then
8177
else
4753))
else
(if i.val < 6262 then
(if i.val < 6261 then
7513
else
6361)
else
(if i.val < 6263 then
7415
else
5172)))
else
(if i.val < 6268 then
(if i.val < 6266 then
(if i.val < 6265 then
3086
else
8178)
else
(if i.val < 6267 then
7408
else
8179))
else
(if i.val < 6270 then
(if i.val < 6269 then
8180
else
7560)
else
(if i.val < 6271 then
8079
else
2811)))))))
else
(if i.val < 6336 then
(if i.val < 6304 then
(if i.val < 6288 then
(if i.val < 6280 then
(if i.val < 6276 then
(if i.val < 6274 then
(if i.val < 6273 then
7965
else
7615)
else
(if i.val < 6275 then
5602
else
2692))
else
(if i.val < 6278 then
(if i.val < 6277 then
1331
else
7621)
else
(if i.val < 6279 then
5369
else
5105)))
else
(if i.val < 6284 then
(if i.val < 6282 then
(if i.val < 6281 then
2498
else
8181)
else
(if i.val < 6283 then
3100
else
6084))
else
(if i.val < 6286 then
(if i.val < 6285 then
5619
else
3313)
else
(if i.val < 6287 then
6463
else
7552))))
else
(if i.val < 6296 then
(if i.val < 6292 then
(if i.val < 6290 then
(if i.val < 6289 then
8124
else
5566)
else
(if i.val < 6291 then
5907
else
8125))
else
(if i.val < 6294 then
(if i.val < 6293 then
1000
else
1001)
else
(if i.val < 6295 then
1002
else
1458)))
else
(if i.val < 6300 then
(if i.val < 6298 then
(if i.val < 6297 then
1460
else
1461)
else
(if i.val < 6299 then
1470
else
1476))
else
(if i.val < 6302 then
(if i.val < 6301 then
1485
else
983)
else
(if i.val < 6303 then
987
else
1138)))))
else
(if i.val < 6320 then
(if i.val < 6312 then
(if i.val < 6308 then
(if i.val < 6306 then
(if i.val < 6305 then
1140
else
1141)
else
(if i.val < 6307 then
1146
else
1147))
else
(if i.val < 6310 then
(if i.val < 6309 then
1152
else
1153)
else
(if i.val < 6311 then
1500
else
1503)))
else
(if i.val < 6316 then
(if i.val < 6314 then
(if i.val < 6313 then
1505
else
1512)
else
(if i.val < 6315 then
1514
else
1538))
else
(if i.val < 6318 then
(if i.val < 6317 then
1692
else
1693)
else
(if i.val < 6319 then
1696
else
1701))))
else
(if i.val < 6328 then
(if i.val < 6324 then
(if i.val < 6322 then
(if i.val < 6321 then
1722
else
7488)
else
(if i.val < 6323 then
7605
else
7900))
else
(if i.val < 6326 then
(if i.val < 6325 then
8126
else
3095)
else
(if i.val < 6327 then
4930
else
5297)))
else
(if i.val < 6332 then
(if i.val < 6330 then
(if i.val < 6329 then
8213
else
5206)
else
(if i.val < 6331 then
3592
else
8185))
else
(if i.val < 6334 then
(if i.val < 6333 then
3569
else
5638)
else
(if i.val < 6335 then
2640
else
8063))))))
else
(if i.val < 6368 then
(if i.val < 6352 then
(if i.val < 6344 then
(if i.val < 6340 then
(if i.val < 6338 then
(if i.val < 6337 then
8003
else
6894)
else
(if i.val < 6339 then
8249
else
5672))
else
(if i.val < 6342 then
(if i.val < 6341 then
4294
else
2872)
else
(if i.val < 6343 then
7607
else
3366)))
else
(if i.val < 6348 then
(if i.val < 6346 then
(if i.val < 6345 then
7993
else
7357)
else
(if i.val < 6347 then
5544
else
8127))
else
(if i.val < 6350 then
(if i.val < 6349 then
7899
else
8259)
else
(if i.val < 6351 then
8211
else
7449))))
else
(if i.val < 6360 then
(if i.val < 6356 then
(if i.val < 6354 then
(if i.val < 6353 then
8086
else
3107)
else
(if i.val < 6355 then
8323
else
8324))
else
(if i.val < 6358 then
(if i.val < 6357 then
7824
else
5605)
else
(if i.val < 6359 then
7968
else
2456)))
else
(if i.val < 6364 then
(if i.val < 6362 then
(if i.val < 6361 then
7976
else
2535)
else
(if i.val < 6363 then
4757
else
2454))
else
(if i.val < 6366 then
(if i.val < 6365 then
7527
else
2457)
else
(if i.val < 6367 then
7797
else
3412)))))
else
(if i.val < 6384 then
(if i.val < 6376 then
(if i.val < 6372 then
(if i.val < 6370 then
(if i.val < 6369 then
7998
else
4443)
else
(if i.val < 6371 then
7423
else
4598))
else
(if i.val < 6374 then
(if i.val < 6373 then
7695
else
5759)
else
(if i.val < 6375 then
4621
else
3822)))
else
(if i.val < 6380 then
(if i.val < 6378 then
(if i.val < 6377 then
8071
else
6368)
else
(if i.val < 6379 then
3818
else
8325))
else
(if i.val < 6382 then
(if i.val < 6381 then
8204
else
3585)
else
(if i.val < 6383 then
7233
else
2710))))
else
(if i.val < 6392 then
(if i.val < 6388 then
(if i.val < 6386 then
(if i.val < 6385 then
7610
else
1325)
else
(if i.val < 6387 then
2490
else
3817))
else
(if i.val < 6390 then
(if i.val < 6389 then
8276
else
7053)
else
(if i.val < 6391 then
7687
else
6146)))
else
(if i.val < 6396 then
(if i.val < 6394 then
(if i.val < 6393 then
6490
else
6511)
else
(if i.val < 6395 then
5660
else
8326))
else
(if i.val < 6398 then
(if i.val < 6397 then
3150
else
3595)
else
(if i.val < 6399 then
5956
else
8269))))))))
else
(if i.val < 6528 then
(if i.val < 6464 then
(if i.val < 6432 then
(if i.val < 6416 then
(if i.val < 6408 then
(if i.val < 6404 then
(if i.val < 6402 then
(if i.val < 6401 then
4482
else
8231)
else
(if i.val < 6403 then
6365
else
8252))
else
(if i.val < 6406 then
(if i.val < 6405 then
6563
else
5224)
else
(if i.val < 6407 then
2752
else
3416)))
else
(if i.val < 6412 then
(if i.val < 6410 then
(if i.val < 6409 then
8053
else
8277)
else
(if i.val < 6411 then
3216
else
2714))
else
(if i.val < 6414 then
(if i.val < 6413 then
3143
else
5870)
else
(if i.val < 6415 then
1887
else
6107))))
else
(if i.val < 6424 then
(if i.val < 6420 then
(if i.val < 6418 then
(if i.val < 6417 then
6836
else
3345)
else
(if i.val < 6419 then
6518
else
3406))
else
(if i.val < 6422 then
(if i.val < 6421 then
3319
else
3410)
else
(if i.val < 6423 then
4801
else
5075)))
else
(if i.val < 6428 then
(if i.val < 6426 then
(if i.val < 6425 then
8059
else
5565)
else
(if i.val < 6427 then
6856
else
3115))
else
(if i.val < 6430 then
(if i.val < 6429 then
5009
else
6835)
else
(if i.val < 6431 then
8275
else
8208)))))
else
(if i.val < 6448 then
(if i.val < 6440 then
(if i.val < 6436 then
(if i.val < 6434 then
(if i.val < 6433 then
2283
else
8262)
else
(if i.val < 6435 then
1305
else
2794))
else
(if i.val < 6438 then
(if i.val < 6437 then
2830
else
4418)
else
(if i.val < 6439 then
3868
else
6326)))
else
(if i.val < 6444 then
(if i.val < 6442 then
(if i.val < 6441 then
4328
else
4302)
else
(if i.val < 6443 then
2715
else
2288))
else
(if i.val < 6446 then
(if i.val < 6445 then
7543
else
8248)
else
(if i.val < 6447 then
7782
else
4570))))
else
(if i.val < 6456 then
(if i.val < 6452 then
(if i.val < 6450 then
(if i.val < 6449 then
5984
else
7971)
else
(if i.val < 6451 then
4433
else
3362))
else
(if i.val < 6454 then
(if i.val < 6453 then
7997
else
2866)
else
(if i.val < 6455 then
7223
else
6933)))
else
(if i.val < 6460 then
(if i.val < 6458 then
(if i.val < 6457 then
4057
else
7608)
else
(if i.val < 6459 then
3885
else
8087))
else
(if i.val < 6462 then
(if i.val < 6461 then
2406
else
5260)
else
(if i.val < 6463 then
5874
else
3591))))))
else
(if i.val < 6496 then
(if i.val < 6480 then
(if i.val < 6472 then
(if i.val < 6468 then
(if i.val < 6466 then
(if i.val < 6465 then
7860
else
3799)
else
(if i.val < 6467 then
7424
else
6128))
else
(if i.val < 6470 then
(if i.val < 6469 then
5235
else
4931)
else
(if i.val < 6471 then
7565
else
2666)))
else
(if i.val < 6476 then
(if i.val < 6474 then
(if i.val < 6473 then
8327
else
8202)
else
(if i.val < 6475 then
4984
else
2875))
else
(if i.val < 6478 then
(if i.val < 6477 then
4604
else
1233)
else
(if i.val < 6479 then
5052
else
5044))))
else
(if i.val < 6488 then
(if i.val < 6484 then
(if i.val < 6482 then
(if i.val < 6481 then
8328
else
5607)
else
(if i.val < 6483 then
1360
else
6458))
else
(if i.val < 6486 then
(if i.val < 6485 then
7224
else
7653)
else
(if i.val < 6487 then
7096
else
3435)))
else
(if i.val < 6492 then
(if i.val < 6490 then
(if i.val < 6489 then
8329
else
7414)
else
(if i.val < 6491 then
8330
else
8102))
else
(if i.val < 6494 then
(if i.val < 6493 then
7828
else
2398)
else
(if i.val < 6495 then
5847
else
5977)))))
else
(if i.val < 6512 then
(if i.val < 6504 then
(if i.val < 6500 then
(if i.val < 6498 then
(if i.val < 6497 then
2378
else
2825)
else
(if i.val < 6499 then
8240
else
7088))
else
(if i.val < 6502 then
(if i.val < 6501 then
3439
else
5897)
else
(if i.val < 6503 then
5715
else
5376)))
else
(if i.val < 6508 then
(if i.val < 6506 then
(if i.val < 6505 then
5293
else
4562)
else
(if i.val < 6507 then
5249
else
2033))
else
(if i.val < 6510 then
(if i.val < 6509 then
5639
else
5256)
else
(if i.val < 6511 then
5703
else
8331))))
else
(if i.val < 6520 then
(if i.val < 6516 then
(if i.val < 6514 then
(if i.val < 6513 then
7065
else
8251)
else
(if i.val < 6515 then
8253
else
7049))
else
(if i.val < 6518 then
(if i.val < 6517 then
7802
else
4676)
else
(if i.val < 6519 then
8332
else
4599)))
else
(if i.val < 6524 then
(if i.val < 6522 then
(if i.val < 6521 then
4008
else
3674)
else
(if i.val < 6523 then
6204
else
4720))
else
(if i.val < 6526 then
(if i.val < 6525 then
5201
else
7219)
else
(if i.val < 6527 then
1376
else
2035)))))))
else
(if i.val < 6592 then
(if i.val < 6560 then
(if i.val < 6544 then
(if i.val < 6536 then
(if i.val < 6532 then
(if i.val < 6530 then
(if i.val < 6529 then
2034
else
2029)
else
(if i.val < 6531 then
2025
else
6081))
else
(if i.val < 6534 then
(if i.val < 6533 then
8255
else
1967)
else
(if i.val < 6535 then
3187
else
6911)))
else
(if i.val < 6540 then
(if i.val < 6538 then
(if i.val < 6537 then
8256
else
1066)
else
(if i.val < 6539 then
4975
else
4353))
else
(if i.val < 6542 then
(if i.val < 6541 then
6872
else
6915)
else
(if i.val < 6543 then
4727
else
7649))))
else
(if i.val < 6552 then
(if i.val < 6548 then
(if i.val < 6546 then
(if i.val < 6545 then
2269
else
3584)
else
(if i.val < 6547 then
1078
else
1089))
else
(if i.val < 6550 then
(if i.val < 6549 then
5835
else
5811)
else
(if i.val < 6551 then
8260
else
6519)))
else
(if i.val < 6556 then
(if i.val < 6554 then
(if i.val < 6553 then
4358
else
5214)
else
(if i.val < 6555 then
4409
else
7809))
else
(if i.val < 6558 then
(if i.val < 6557 then
5853
else
3074)
else
(if i.val < 6559 then
8266
else
1984)))))
else
(if i.val < 6576 then
(if i.val < 6568 then
(if i.val < 6564 then
(if i.val < 6562 then
(if i.val < 6561 then
7374
else
7306)
else
(if i.val < 6563 then
7872
else
8271))
else
(if i.val < 6566 then
(if i.val < 6565 then
7811
else
1897)
else
(if i.val < 6567 then
1898
else
1990)))
else
(if i.val < 6572 then
(if i.val < 6570 then
(if i.val < 6569 then
1361
else
1992)
else
(if i.val < 6571 then
6954
else
8233))
else
(if i.val < 6574 then
(if i.val < 6573 then
2396
else
2835)
else
(if i.val < 6575 then
7427
else
1225))))
else
(if i.val < 6584 then
(if i.val < 6580 then
(if i.val < 6578 then
(if i.val < 6577 then
7426
else
5831)
else
(if i.val < 6579 then
6875
else
7825))
else
(if i.val < 6582 then
(if i.val < 6581 then
7277
else
7539)
else
(if i.val < 6583 then
7440
else
5743)))
else
(if i.val < 6588 then
(if i.val < 6586 then
(if i.val < 6585 then
8084
else
7281)
else
(if i.val < 6587 then
8205
else
7679))
else
(if i.val < 6590 then
(if i.val < 6589 then
1294
else
1079)
else
(if i.val < 6591 then
1313
else
1080))))))
else
(if i.val < 6624 then
(if i.val < 6608 then
(if i.val < 6600 then
(if i.val < 6596 then
(if i.val < 6594 then
(if i.val < 6593 then
1056
else
3369)
else
(if i.val < 6595 then
7677
else
1379))
else
(if i.val < 6598 then
(if i.val < 6597 then
7508
else
8278)
else
(if i.val < 6599 then
2728
else
5390)))
else
(if i.val < 6604 then
(if i.val < 6602 then
(if i.val < 6601 then
6465
else
5037)
else
(if i.val < 6603 then
7626
else
7686))
else
(if i.val < 6606 then
(if i.val < 6605 then
1891
else
1850)
else
(if i.val < 6607 then
1851
else
1869))))
else
(if i.val < 6616 then
(if i.val < 6612 then
(if i.val < 6610 then
(if i.val < 6609 then
1048
else
1909)
else
(if i.val < 6611 then
1915
else
1375))
else
(if i.val < 6614 then
(if i.val < 6613 then
2024
else
2027)
else
(if i.val < 6615 then
7480
else
7039)))
else
(if i.val < 6620 then
(if i.val < 6618 then
(if i.val < 6617 then
3673
else
7947)
else
(if i.val < 6619 then
3996
else
7264))
else
(if i.val < 6622 then
(if i.val < 6621 then
7211
else
7307)
else
(if i.val < 6623 then
1197
else
3803)))))
else
(if i.val < 6640 then
(if i.val < 6632 then
(if i.val < 6628 then
(if i.val < 6626 then
(if i.val < 6625 then
1935
else
1953)
else
(if i.val < 6627 then
4544
else
8246))
else
(if i.val < 6630 then
(if i.val < 6629 then
7222
else
1950)
else
(if i.val < 6631 then
6339
else
8130)))
else
(if i.val < 6636 then
(if i.val < 6634 then
(if i.val < 6633 then
7378
else
7826)
else
(if i.val < 6635 then
1920
else
1342))
else
(if i.val < 6638 then
(if i.val < 6637 then
1334
else
1071)
else
(if i.val < 6639 then
1070
else
4958))))
else
(if i.val < 6648 then
(if i.val < 6644 then
(if i.val < 6642 then
(if i.val < 6641 then
7500
else
3675)
else
(if i.val < 6643 then
4315
else
1927))
else
(if i.val < 6646 then
(if i.val < 6645 then
1067
else
4967)
else
(if i.val < 6647 then
8016
else
2656)))
else
(if i.val < 6652 then
(if i.val < 6650 then
(if i.val < 6649 then
4999
else
4351)
else
(if i.val < 6651 then
4605
else
7388))
else
(if i.val < 6654 then
(if i.val < 6653 then
6994
else
6544)
else
(if i.val < 6655 then
8333
else
4426)))))))))

end HodgeLean.Foundations.Program

end
