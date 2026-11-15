import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixPacked0650
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow06
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row06_cosetRepresentatives : Fin 1080 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 512 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row06_cosetRepresentativesPart0000 i
else
g32p_row06_cosetRepresentativesPart0001 i)
else
(if i.val < 384 then
g32p_row06_cosetRepresentativesPart0002 i
else
g32p_row06_cosetRepresentativesPart0003 i))
else
(if i.val < 768 then
(if i.val < 640 then
g32p_row06_cosetRepresentativesPart0004 i
else
g32p_row06_cosetRepresentativesPart0005 i)
else
(if i.val < 896 then
g32p_row06_cosetRepresentativesPart0006 i
else
(if i.val < 1024 then
g32p_row06_cosetRepresentativesPart0007 i
else
g32p_row06_cosetRepresentativesPart0008 i))))

def g32p_row06_cosetWords : Fin 1080 → List (Fin 4) :=
  fun i => (if i.val < 512 then
(if i.val < 256 then
(if i.val < 128 then
g32p_row06_cosetWordsPart0000 i
else
g32p_row06_cosetWordsPart0001 i)
else
(if i.val < 384 then
g32p_row06_cosetWordsPart0002 i
else
g32p_row06_cosetWordsPart0003 i))
else
(if i.val < 768 then
(if i.val < 640 then
g32p_row06_cosetWordsPart0004 i
else
g32p_row06_cosetWordsPart0005 i)
else
(if i.val < 896 then
g32p_row06_cosetWordsPart0006 i
else
(if i.val < 1024 then
g32p_row06_cosetWordsPart0007 i
else
g32p_row06_cosetWordsPart0008 i))))

def g32p_row06_cosetBranchMatrices : Fin 3 → HurwitzPrymRex_Mat :=
  ![![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]], ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]]

def g32p_row06_cosetGeneratorNextColumn0 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
1
else
5)
else
(if i.val < 3 then
6
else
7))
else
(if i.val < 6 then
(if i.val < 5 then
8
else
0)
else
(if i.val < 7 then
19
else
20)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
21
else
22)
else
(if i.val < 11 then
23
else
24))
else
(if i.val < 14 then
(if i.val < 13 then
25
else
26)
else
(if i.val < 15 then
27
else
28))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
29
else
30)
else
(if i.val < 19 then
31
else
2))
else
(if i.val < 22 then
(if i.val < 21 then
3
else
4)
else
(if i.val < 23 then
55
else
56)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
57
else
58)
else
(if i.val < 27 then
59
else
60))
else
(if i.val < 30 then
(if i.val < 29 then
61
else
62)
else
(if i.val < 31 then
63
else
(if i.val < 32 then
64
else
65))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
66
else
67)
else
(if i.val < 36 then
68
else
69))
else
(if i.val < 39 then
(if i.val < 38 then
70
else
71)
else
(if i.val < 40 then
72
else
73)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
74
else
75)
else
(if i.val < 44 then
76
else
77))
else
(if i.val < 47 then
(if i.val < 46 then
78
else
79)
else
(if i.val < 48 then
80
else
(if i.val < 49 then
81
else
82)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
83
else
84)
else
(if i.val < 53 then
85
else
86))
else
(if i.val < 56 then
(if i.val < 55 then
87
else
9)
else
(if i.val < 57 then
10
else
11)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
12
else
13)
else
(if i.val < 61 then
14
else
15))
else
(if i.val < 64 then
(if i.val < 63 then
16
else
17)
else
(if i.val < 65 then
18
else
(if i.val < 66 then
138
else
139)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
140
else
141)
else
(if i.val < 70 then
142
else
143))
else
(if i.val < 73 then
(if i.val < 72 then
144
else
145)
else
(if i.val < 74 then
146
else
147)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
148
else
149)
else
(if i.val < 78 then
150
else
151))
else
(if i.val < 81 then
(if i.val < 80 then
152
else
153)
else
(if i.val < 82 then
154
else
(if i.val < 83 then
155
else
156)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
157
else
158)
else
(if i.val < 87 then
159
else
160))
else
(if i.val < 90 then
(if i.val < 89 then
161
else
162)
else
(if i.val < 91 then
163
else
164)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
165
else
166)
else
(if i.val < 95 then
167
else
168))
else
(if i.val < 98 then
(if i.val < 97 then
169
else
170)
else
(if i.val < 99 then
171
else
(if i.val < 100 then
172
else
173))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
174
else
175)
else
(if i.val < 104 then
176
else
177))
else
(if i.val < 107 then
(if i.val < 106 then
178
else
179)
else
(if i.val < 108 then
180
else
181)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
182
else
183)
else
(if i.val < 112 then
184
else
185))
else
(if i.val < 115 then
(if i.val < 114 then
186
else
187)
else
(if i.val < 116 then
188
else
(if i.val < 117 then
189
else
190)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
191
else
192)
else
(if i.val < 121 then
193
else
194))
else
(if i.val < 124 then
(if i.val < 123 then
195
else
196)
else
(if i.val < 125 then
197
else
198)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
199
else
200)
else
(if i.val < 129 then
201
else
202))
else
(if i.val < 132 then
(if i.val < 131 then
203
else
204)
else
(if i.val < 133 then
205
else
(if i.val < 134 then
206
else
207))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
208
else
209)
else
(if i.val < 138 then
210
else
32))
else
(if i.val < 141 then
(if i.val < 140 then
33
else
34)
else
(if i.val < 142 then
35
else
36)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
37
else
38)
else
(if i.val < 146 then
39
else
40))
else
(if i.val < 149 then
(if i.val < 148 then
41
else
42)
else
(if i.val < 150 then
43
else
44))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
45
else
46)
else
(if i.val < 154 then
47
else
48))
else
(if i.val < 157 then
(if i.val < 156 then
49
else
50)
else
(if i.val < 158 then
51
else
52)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
53
else
54)
else
(if i.val < 162 then
295
else
296))
else
(if i.val < 165 then
(if i.val < 164 then
297
else
298)
else
(if i.val < 166 then
299
else
(if i.val < 167 then
300
else
301))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
302
else
303)
else
(if i.val < 171 then
304
else
305))
else
(if i.val < 174 then
(if i.val < 173 then
306
else
307)
else
(if i.val < 175 then
308
else
309)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
310
else
311)
else
(if i.val < 179 then
312
else
313))
else
(if i.val < 182 then
(if i.val < 181 then
314
else
315)
else
(if i.val < 183 then
316
else
(if i.val < 184 then
317
else
318)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
319
else
320)
else
(if i.val < 188 then
321
else
322))
else
(if i.val < 191 then
(if i.val < 190 then
323
else
324)
else
(if i.val < 192 then
325
else
326)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
327
else
328)
else
(if i.val < 196 then
329
else
330))
else
(if i.val < 199 then
(if i.val < 198 then
331
else
332)
else
(if i.val < 200 then
333
else
(if i.val < 201 then
334
else
335)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
336
else
337)
else
(if i.val < 205 then
338
else
339))
else
(if i.val < 208 then
(if i.val < 207 then
340
else
341)
else
(if i.val < 209 then
342
else
343)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
344
else
345)
else
(if i.val < 213 then
346
else
347))
else
(if i.val < 216 then
(if i.val < 215 then
348
else
349)
else
(if i.val < 217 then
350
else
(if i.val < 218 then
351
else
352)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
353
else
354)
else
(if i.val < 222 then
355
else
356))
else
(if i.val < 225 then
(if i.val < 224 then
357
else
358)
else
(if i.val < 226 then
359
else
360)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
361
else
362)
else
(if i.val < 230 then
363
else
364))
else
(if i.val < 233 then
(if i.val < 232 then
365
else
366)
else
(if i.val < 234 then
367
else
(if i.val < 235 then
368
else
369))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
370
else
371)
else
(if i.val < 239 then
372
else
373))
else
(if i.val < 242 then
(if i.val < 241 then
374
else
375)
else
(if i.val < 243 then
376
else
377)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
378
else
379)
else
(if i.val < 247 then
380
else
381))
else
(if i.val < 250 then
(if i.val < 249 then
382
else
383)
else
(if i.val < 251 then
384
else
(if i.val < 252 then
385
else
386)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
387
else
388)
else
(if i.val < 256 then
389
else
390))
else
(if i.val < 259 then
(if i.val < 258 then
391
else
392)
else
(if i.val < 260 then
393
else
394)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
395
else
396)
else
(if i.val < 264 then
397
else
398))
else
(if i.val < 267 then
(if i.val < 266 then
399
else
400)
else
(if i.val < 268 then
401
else
(if i.val < 269 then
402
else
403)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
404
else
405)
else
(if i.val < 273 then
406
else
407))
else
(if i.val < 276 then
(if i.val < 275 then
408
else
409)
else
(if i.val < 277 then
410
else
411)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
412
else
413)
else
(if i.val < 281 then
414
else
415))
else
(if i.val < 284 then
(if i.val < 283 then
416
else
417)
else
(if i.val < 285 then
418
else
419))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
420
else
421)
else
(if i.val < 289 then
422
else
423))
else
(if i.val < 292 then
(if i.val < 291 then
424
else
425)
else
(if i.val < 293 then
426
else
427)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
428
else
88)
else
(if i.val < 297 then
89
else
90))
else
(if i.val < 300 then
(if i.val < 299 then
91
else
92)
else
(if i.val < 301 then
93
else
(if i.val < 302 then
94
else
95))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
96
else
97)
else
(if i.val < 306 then
98
else
99))
else
(if i.val < 309 then
(if i.val < 308 then
100
else
101)
else
(if i.val < 310 then
102
else
103)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
104
else
105)
else
(if i.val < 314 then
106
else
107))
else
(if i.val < 317 then
(if i.val < 316 then
108
else
109)
else
(if i.val < 318 then
110
else
(if i.val < 319 then
111
else
112)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
113
else
114)
else
(if i.val < 323 then
115
else
116))
else
(if i.val < 326 then
(if i.val < 325 then
117
else
118)
else
(if i.val < 327 then
119
else
120)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
121
else
122)
else
(if i.val < 331 then
123
else
124))
else
(if i.val < 334 then
(if i.val < 333 then
125
else
126)
else
(if i.val < 335 then
127
else
(if i.val < 336 then
128
else
129)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
130
else
131)
else
(if i.val < 340 then
132
else
133))
else
(if i.val < 343 then
(if i.val < 342 then
134
else
135)
else
(if i.val < 344 then
136
else
137)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
537
else
538)
else
(if i.val < 348 then
539
else
540))
else
(if i.val < 351 then
(if i.val < 350 then
541
else
542)
else
(if i.val < 352 then
543
else
(if i.val < 353 then
544
else
545)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
546
else
547)
else
(if i.val < 357 then
548
else
549))
else
(if i.val < 360 then
(if i.val < 359 then
550
else
551)
else
(if i.val < 361 then
552
else
553)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
554
else
555)
else
(if i.val < 365 then
556
else
557))
else
(if i.val < 368 then
(if i.val < 367 then
558
else
559)
else
(if i.val < 369 then
560
else
(if i.val < 370 then
561
else
562))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
563
else
564)
else
(if i.val < 374 then
565
else
566))
else
(if i.val < 377 then
(if i.val < 376 then
567
else
568)
else
(if i.val < 378 then
569
else
570)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
571
else
572)
else
(if i.val < 382 then
573
else
574))
else
(if i.val < 385 then
(if i.val < 384 then
575
else
576)
else
(if i.val < 386 then
577
else
(if i.val < 387 then
578
else
579)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
580
else
581)
else
(if i.val < 391 then
582
else
583))
else
(if i.val < 394 then
(if i.val < 393 then
584
else
585)
else
(if i.val < 395 then
586
else
587)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
588
else
589)
else
(if i.val < 399 then
590
else
591))
else
(if i.val < 402 then
(if i.val < 401 then
592
else
593)
else
(if i.val < 403 then
594
else
(if i.val < 404 then
595
else
596))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
597
else
598)
else
(if i.val < 408 then
599
else
600))
else
(if i.val < 411 then
(if i.val < 410 then
601
else
602)
else
(if i.val < 412 then
603
else
604)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
605
else
606)
else
(if i.val < 416 then
607
else
608))
else
(if i.val < 419 then
(if i.val < 418 then
609
else
610)
else
(if i.val < 420 then
611
else
612))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
613
else
614)
else
(if i.val < 424 then
615
else
616))
else
(if i.val < 427 then
(if i.val < 426 then
617
else
618)
else
(if i.val < 428 then
619
else
620)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
621
else
622)
else
(if i.val < 432 then
623
else
624))
else
(if i.val < 435 then
(if i.val < 434 then
625
else
626)
else
(if i.val < 436 then
627
else
(if i.val < 437 then
628
else
629))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
630
else
631)
else
(if i.val < 441 then
632
else
633))
else
(if i.val < 444 then
(if i.val < 443 then
634
else
635)
else
(if i.val < 445 then
636
else
637)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
638
else
639)
else
(if i.val < 449 then
640
else
641))
else
(if i.val < 452 then
(if i.val < 451 then
642
else
643)
else
(if i.val < 453 then
644
else
(if i.val < 454 then
645
else
646)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
647
else
648)
else
(if i.val < 458 then
649
else
650))
else
(if i.val < 461 then
(if i.val < 460 then
651
else
652)
else
(if i.val < 462 then
653
else
654)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
655
else
656)
else
(if i.val < 466 then
657
else
658))
else
(if i.val < 469 then
(if i.val < 468 then
659
else
660)
else
(if i.val < 470 then
661
else
(if i.val < 471 then
662
else
663)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
664
else
665)
else
(if i.val < 475 then
666
else
667))
else
(if i.val < 478 then
(if i.val < 477 then
668
else
669)
else
(if i.val < 479 then
670
else
671)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
672
else
673)
else
(if i.val < 483 then
674
else
675))
else
(if i.val < 486 then
(if i.val < 485 then
676
else
677)
else
(if i.val < 487 then
678
else
(if i.val < 488 then
679
else
680)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
681
else
682)
else
(if i.val < 492 then
683
else
684))
else
(if i.val < 495 then
(if i.val < 494 then
685
else
686)
else
(if i.val < 496 then
687
else
688)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
689
else
690)
else
(if i.val < 500 then
691
else
692))
else
(if i.val < 503 then
(if i.val < 502 then
693
else
694)
else
(if i.val < 504 then
695
else
(if i.val < 505 then
696
else
697))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
698
else
699)
else
(if i.val < 509 then
700
else
701))
else
(if i.val < 512 then
(if i.val < 511 then
702
else
703)
else
(if i.val < 513 then
704
else
705)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
706
else
707)
else
(if i.val < 517 then
708
else
709))
else
(if i.val < 520 then
(if i.val < 519 then
710
else
711)
else
(if i.val < 521 then
712
else
(if i.val < 522 then
713
else
714)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
715
else
716)
else
(if i.val < 526 then
717
else
718))
else
(if i.val < 529 then
(if i.val < 528 then
719
else
720)
else
(if i.val < 530 then
721
else
722)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
723
else
724)
else
(if i.val < 534 then
725
else
726))
else
(if i.val < 537 then
(if i.val < 536 then
727
else
728)
else
(if i.val < 538 then
211
else
(if i.val < 539 then
212
else
213))))))))))
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
214
else
215)
else
(if i.val < 543 then
216
else
217))
else
(if i.val < 546 then
(if i.val < 545 then
218
else
219)
else
(if i.val < 547 then
220
else
221)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
222
else
223)
else
(if i.val < 551 then
224
else
225))
else
(if i.val < 554 then
(if i.val < 553 then
226
else
227)
else
(if i.val < 555 then
228
else
229))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
230
else
231)
else
(if i.val < 559 then
232
else
233))
else
(if i.val < 562 then
(if i.val < 561 then
234
else
235)
else
(if i.val < 563 then
236
else
237)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
238
else
239)
else
(if i.val < 567 then
240
else
241))
else
(if i.val < 570 then
(if i.val < 569 then
242
else
243)
else
(if i.val < 571 then
244
else
(if i.val < 572 then
245
else
246))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
247
else
248)
else
(if i.val < 576 then
249
else
250))
else
(if i.val < 579 then
(if i.val < 578 then
251
else
252)
else
(if i.val < 580 then
253
else
254)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
255
else
256)
else
(if i.val < 584 then
257
else
258))
else
(if i.val < 587 then
(if i.val < 586 then
259
else
260)
else
(if i.val < 588 then
261
else
(if i.val < 589 then
262
else
263)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
264
else
265)
else
(if i.val < 593 then
266
else
267))
else
(if i.val < 596 then
(if i.val < 595 then
268
else
269)
else
(if i.val < 597 then
270
else
271)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
272
else
273)
else
(if i.val < 601 then
274
else
275))
else
(if i.val < 604 then
(if i.val < 603 then
276
else
277)
else
(if i.val < 605 then
278
else
(if i.val < 606 then
279
else
280)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
281
else
282)
else
(if i.val < 610 then
283
else
284))
else
(if i.val < 613 then
(if i.val < 612 then
285
else
286)
else
(if i.val < 614 then
287
else
288)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
289
else
290)
else
(if i.val < 618 then
291
else
292))
else
(if i.val < 621 then
(if i.val < 620 then
293
else
294)
else
(if i.val < 622 then
795
else
(if i.val < 623 then
796
else
797)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
798
else
799)
else
(if i.val < 627 then
800
else
801))
else
(if i.val < 630 then
(if i.val < 629 then
802
else
803)
else
(if i.val < 631 then
804
else
805)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
806
else
807)
else
(if i.val < 635 then
808
else
809))
else
(if i.val < 638 then
(if i.val < 637 then
810
else
811)
else
(if i.val < 639 then
812
else
(if i.val < 640 then
813
else
814))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
815
else
816)
else
(if i.val < 644 then
817
else
818))
else
(if i.val < 647 then
(if i.val < 646 then
819
else
820)
else
(if i.val < 648 then
821
else
822)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
823
else
824)
else
(if i.val < 652 then
825
else
826))
else
(if i.val < 655 then
(if i.val < 654 then
827
else
828)
else
(if i.val < 656 then
829
else
(if i.val < 657 then
830
else
831)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
832
else
833)
else
(if i.val < 661 then
834
else
835))
else
(if i.val < 664 then
(if i.val < 663 then
836
else
837)
else
(if i.val < 665 then
838
else
839)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
840
else
841)
else
(if i.val < 669 then
842
else
843))
else
(if i.val < 672 then
(if i.val < 671 then
844
else
845)
else
(if i.val < 673 then
846
else
(if i.val < 674 then
847
else
848))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
849
else
850)
else
(if i.val < 678 then
851
else
852))
else
(if i.val < 681 then
(if i.val < 680 then
853
else
854)
else
(if i.val < 682 then
855
else
856)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
857
else
858)
else
(if i.val < 686 then
859
else
860))
else
(if i.val < 689 then
(if i.val < 688 then
861
else
862)
else
(if i.val < 690 then
863
else
864))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
865
else
866)
else
(if i.val < 694 then
867
else
868))
else
(if i.val < 697 then
(if i.val < 696 then
869
else
870)
else
(if i.val < 698 then
871
else
872)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
873
else
874)
else
(if i.val < 702 then
875
else
876))
else
(if i.val < 705 then
(if i.val < 704 then
877
else
878)
else
(if i.val < 706 then
879
else
(if i.val < 707 then
880
else
881))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
882
else
883)
else
(if i.val < 711 then
884
else
885))
else
(if i.val < 714 then
(if i.val < 713 then
886
else
887)
else
(if i.val < 715 then
888
else
889)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
890
else
891)
else
(if i.val < 719 then
892
else
893))
else
(if i.val < 722 then
(if i.val < 721 then
894
else
895)
else
(if i.val < 723 then
896
else
(if i.val < 724 then
897
else
898)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
899
else
900)
else
(if i.val < 728 then
901
else
902))
else
(if i.val < 731 then
(if i.val < 730 then
903
else
904)
else
(if i.val < 732 then
905
else
906)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
907
else
908)
else
(if i.val < 736 then
909
else
910))
else
(if i.val < 739 then
(if i.val < 738 then
911
else
912)
else
(if i.val < 740 then
913
else
(if i.val < 741 then
914
else
915)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
916
else
917)
else
(if i.val < 745 then
918
else
919))
else
(if i.val < 748 then
(if i.val < 747 then
920
else
921)
else
(if i.val < 749 then
922
else
923)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
924
else
925)
else
(if i.val < 753 then
926
else
927))
else
(if i.val < 756 then
(if i.val < 755 then
928
else
929)
else
(if i.val < 757 then
930
else
(if i.val < 758 then
931
else
932)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
933
else
934)
else
(if i.val < 762 then
935
else
936))
else
(if i.val < 765 then
(if i.val < 764 then
937
else
938)
else
(if i.val < 766 then
939
else
940)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
941
else
942)
else
(if i.val < 770 then
943
else
944))
else
(if i.val < 773 then
(if i.val < 772 then
945
else
946)
else
(if i.val < 774 then
947
else
(if i.val < 775 then
948
else
949))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
950
else
951)
else
(if i.val < 779 then
952
else
953))
else
(if i.val < 782 then
(if i.val < 781 then
954
else
955)
else
(if i.val < 783 then
956
else
957)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
958
else
959)
else
(if i.val < 787 then
960
else
961))
else
(if i.val < 790 then
(if i.val < 789 then
962
else
963)
else
(if i.val < 791 then
964
else
(if i.val < 792 then
965
else
966)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
967
else
968)
else
(if i.val < 796 then
429
else
430))
else
(if i.val < 799 then
(if i.val < 798 then
431
else
432)
else
(if i.val < 800 then
433
else
434)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
435
else
436)
else
(if i.val < 804 then
437
else
438))
else
(if i.val < 807 then
(if i.val < 806 then
439
else
440)
else
(if i.val < 808 then
441
else
(if i.val < 809 then
442
else
443)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
444
else
445)
else
(if i.val < 813 then
446
else
447))
else
(if i.val < 816 then
(if i.val < 815 then
448
else
449)
else
(if i.val < 817 then
450
else
451)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
452
else
453)
else
(if i.val < 821 then
454
else
455))
else
(if i.val < 824 then
(if i.val < 823 then
456
else
457)
else
(if i.val < 825 then
458
else
459))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
460
else
461)
else
(if i.val < 829 then
462
else
463))
else
(if i.val < 832 then
(if i.val < 831 then
464
else
465)
else
(if i.val < 833 then
466
else
467)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
468
else
469)
else
(if i.val < 837 then
470
else
471))
else
(if i.val < 840 then
(if i.val < 839 then
472
else
473)
else
(if i.val < 841 then
474
else
(if i.val < 842 then
475
else
476))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
477
else
478)
else
(if i.val < 846 then
479
else
480))
else
(if i.val < 849 then
(if i.val < 848 then
481
else
482)
else
(if i.val < 850 then
483
else
484)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
485
else
486)
else
(if i.val < 854 then
487
else
488))
else
(if i.val < 857 then
(if i.val < 856 then
489
else
490)
else
(if i.val < 858 then
491
else
(if i.val < 859 then
492
else
493)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
494
else
495)
else
(if i.val < 863 then
496
else
497))
else
(if i.val < 866 then
(if i.val < 865 then
498
else
499)
else
(if i.val < 867 then
500
else
501)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
502
else
503)
else
(if i.val < 871 then
504
else
505))
else
(if i.val < 874 then
(if i.val < 873 then
506
else
507)
else
(if i.val < 875 then
508
else
(if i.val < 876 then
509
else
510)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
511
else
512)
else
(if i.val < 880 then
513
else
514))
else
(if i.val < 883 then
(if i.val < 882 then
515
else
516)
else
(if i.val < 884 then
517
else
518)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
519
else
520)
else
(if i.val < 888 then
521
else
522))
else
(if i.val < 891 then
(if i.val < 890 then
523
else
524)
else
(if i.val < 892 then
525
else
(if i.val < 893 then
526
else
527)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
528
else
529)
else
(if i.val < 897 then
530
else
531))
else
(if i.val < 900 then
(if i.val < 899 then
532
else
533)
else
(if i.val < 901 then
534
else
535)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
536
else
984)
else
(if i.val < 905 then
985
else
986))
else
(if i.val < 908 then
(if i.val < 907 then
987
else
988)
else
(if i.val < 909 then
989
else
(if i.val < 910 then
990
else
991))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
992
else
993)
else
(if i.val < 914 then
994
else
995))
else
(if i.val < 917 then
(if i.val < 916 then
996
else
997)
else
(if i.val < 918 then
998
else
999)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
1000
else
1001)
else
(if i.val < 922 then
1002
else
1003))
else
(if i.val < 925 then
(if i.val < 924 then
1004
else
1005)
else
(if i.val < 926 then
1006
else
(if i.val < 927 then
1007
else
1008)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
1009
else
1010)
else
(if i.val < 931 then
1011
else
1012))
else
(if i.val < 934 then
(if i.val < 933 then
1013
else
1014)
else
(if i.val < 935 then
1015
else
1016)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1017
else
1018)
else
(if i.val < 939 then
1019
else
1020))
else
(if i.val < 942 then
(if i.val < 941 then
1021
else
1022)
else
(if i.val < 943 then
1023
else
(if i.val < 944 then
1024
else
1025))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
1026
else
1027)
else
(if i.val < 948 then
1028
else
1029))
else
(if i.val < 951 then
(if i.val < 950 then
1030
else
1031)
else
(if i.val < 952 then
1032
else
1033)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
1034
else
1035)
else
(if i.val < 956 then
1036
else
1037))
else
(if i.val < 959 then
(if i.val < 958 then
1038
else
1039)
else
(if i.val < 960 then
1040
else
1041))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
1042
else
1043)
else
(if i.val < 964 then
1044
else
1045))
else
(if i.val < 967 then
(if i.val < 966 then
1046
else
1047)
else
(if i.val < 968 then
1048
else
1049)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
1050
else
1051)
else
(if i.val < 972 then
1052
else
1053))
else
(if i.val < 975 then
(if i.val < 974 then
1054
else
1055)
else
(if i.val < 976 then
1056
else
(if i.val < 977 then
1057
else
1058))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
1059
else
1060)
else
(if i.val < 981 then
1061
else
1062))
else
(if i.val < 984 then
(if i.val < 983 then
1063
else
1064)
else
(if i.val < 985 then
729
else
730)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
731
else
732)
else
(if i.val < 989 then
733
else
734))
else
(if i.val < 992 then
(if i.val < 991 then
735
else
736)
else
(if i.val < 993 then
737
else
(if i.val < 994 then
738
else
739)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
740
else
741)
else
(if i.val < 998 then
742
else
743))
else
(if i.val < 1001 then
(if i.val < 1000 then
744
else
745)
else
(if i.val < 1002 then
746
else
747)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
748
else
749)
else
(if i.val < 1006 then
750
else
751))
else
(if i.val < 1009 then
(if i.val < 1008 then
752
else
753)
else
(if i.val < 1010 then
754
else
(if i.val < 1011 then
755
else
756)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
757
else
758)
else
(if i.val < 1015 then
759
else
760))
else
(if i.val < 1018 then
(if i.val < 1017 then
761
else
762)
else
(if i.val < 1019 then
763
else
764)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
765
else
766)
else
(if i.val < 1023 then
767
else
768))
else
(if i.val < 1026 then
(if i.val < 1025 then
769
else
770)
else
(if i.val < 1027 then
771
else
(if i.val < 1028 then
772
else
773)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
774
else
775)
else
(if i.val < 1032 then
776
else
777))
else
(if i.val < 1035 then
(if i.val < 1034 then
778
else
779)
else
(if i.val < 1036 then
780
else
781)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
782
else
783)
else
(if i.val < 1040 then
784
else
785))
else
(if i.val < 1043 then
(if i.val < 1042 then
786
else
787)
else
(if i.val < 1044 then
788
else
(if i.val < 1045 then
789
else
790))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
791
else
792)
else
(if i.val < 1049 then
793
else
794))
else
(if i.val < 1052 then
(if i.val < 1051 then
1065
else
1066)
else
(if i.val < 1053 then
1067
else
1068)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
1069
else
1070)
else
(if i.val < 1057 then
1071
else
1072))
else
(if i.val < 1060 then
(if i.val < 1059 then
1073
else
1074)
else
(if i.val < 1061 then
1075
else
(if i.val < 1062 then
1076
else
1077)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
1078
else
1079)
else
(if i.val < 1066 then
969
else
970))
else
(if i.val < 1069 then
(if i.val < 1068 then
971
else
972)
else
(if i.val < 1070 then
973
else
974)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
975
else
976)
else
(if i.val < 1074 then
977
else
978))
else
(if i.val < 1077 then
(if i.val < 1076 then
979
else
980)
else
(if i.val < 1078 then
981
else
(if i.val < 1079 then
982
else
983)))))))))))

def g32p_row06_cosetGeneratorNextColumn1 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
2
else
9)
else
(if i.val < 3 then
10
else
11))
else
(if i.val < 6 then
(if i.val < 5 then
12
else
32)
else
(if i.val < 7 then
22
else
33)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
34
else
35)
else
(if i.val < 11 then
0
else
36))
else
(if i.val < 14 then
(if i.val < 13 then
37
else
38)
else
(if i.val < 15 then
39
else
40))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
41
else
42)
else
(if i.val < 19 then
43
else
88))
else
(if i.val < 22 then
(if i.val < 21 then
89
else
90)
else
(if i.val < 23 then
65
else
55)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
66
else
67)
else
(if i.val < 27 then
91
else
59))
else
(if i.val < 30 then
(if i.val < 29 then
70
else
92)
else
(if i.val < 31 then
93
else
(if i.val < 32 then
94
else
95))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
96
else
97)
else
(if i.val < 36 then
1
else
3))
else
(if i.val < 39 then
(if i.val < 38 then
4
else
72)
else
(if i.val < 40 then
98
else
58)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
99
else
100)
else
(if i.val < 44 then
101
else
102))
else
(if i.val < 47 then
(if i.val < 46 then
103
else
104)
else
(if i.val < 48 then
84
else
(if i.val < 49 then
105
else
106)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
107
else
108)
else
(if i.val < 53 then
109
else
110))
else
(if i.val < 56 then
(if i.val < 55 then
87
else
161)
else
(if i.val < 57 then
141
else
211)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
15
else
212)
else
(if i.val < 61 then
144
else
170))
else
(if i.val < 64 then
(if i.val < 63 then
213
else
214)
else
(if i.val < 65 then
215
else
(if i.val < 66 then
6
else
162)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
163
else
138)
else
(if i.val < 70 then
139
else
140))
else
(if i.val < 73 then
(if i.val < 72 then
164
else
13)
else
(if i.val < 74 then
143
else
165)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
166
else
167)
else
(if i.val < 78 then
216
else
217))
else
(if i.val < 81 then
(if i.val < 80 then
218
else
219)
else
(if i.val < 82 then
197
else
(if i.val < 83 then
220
else
221)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
222
else
223)
else
(if i.val < 87 then
224
else
160))
else
(if i.val < 90 then
(if i.val < 89 then
168
else
225)
else
(if i.val < 91 then
146
else
171)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
226
else
227)
else
(if i.val < 95 then
228
else
5))
else
(if i.val < 98 then
(if i.val < 97 then
7
else
8)
else
(if i.val < 99 then
14
else
(if i.val < 100 then
16
else
17))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
18
else
229)
else
(if i.val < 104 then
230
else
231))
else
(if i.val < 107 then
(if i.val < 106 then
232
else
233)
else
(if i.val < 108 then
234
else
235)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
236
else
237)
else
(if i.val < 112 then
205
else
188))
else
(if i.val < 115 then
(if i.val < 114 then
238
else
145)
else
(if i.val < 116 then
239
else
(if i.val < 117 then
198
else
240)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
241
else
242)
else
(if i.val < 121 then
243
else
244))
else
(if i.val < 124 then
(if i.val < 123 then
245
else
246)
else
(if i.val < 125 then
247
else
248)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
249
else
180)
else
(if i.val < 129 then
209
else
250))
else
(if i.val < 132 then
(if i.val < 131 then
251
else
252)
else
(if i.val < 133 then
150
else
(if i.val < 134 then
253
else
254))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
255
else
256)
else
(if i.val < 138 then
257
else
295))
else
(if i.val < 141 then
(if i.val < 140 then
345
else
28)
else
(if i.val < 142 then
302
else
303)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
304
else
321)
else
(if i.val < 146 then
298
else
21))
else
(if i.val < 149 then
(if i.val < 148 then
425
else
429)
else
(if i.val < 150 then
430
else
431))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
432
else
365)
else
(if i.val < 154 then
433
else
434))
else
(if i.val < 157 then
(if i.val < 156 then
435
else
334)
else
(if i.val < 158 then
353
else
436)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
437
else
54)
else
(if i.val < 162 then
23
else
24))
else
(if i.val < 165 then
(if i.val < 164 then
25
else
346)
else
(if i.val < 166 then
347
else
(if i.val < 167 then
348
else
349))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
19
else
296)
else
(if i.val < 171 then
297
else
26))
else
(if i.val < 174 then
(if i.val < 173 then
299
else
300)
else
(if i.val < 175 then
301
else
350)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
351
else
352)
else
(if i.val < 179 then
331
else
354))
else
(if i.val < 182 then
(if i.val < 181 then
355
else
356)
else
(if i.val < 183 then
357
else
(if i.val < 184 then
358
else
363)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
438
else
439)
else
(if i.val < 188 then
305
else
440))
else
(if i.val < 191 then
(if i.val < 190 then
441
else
442)
else
(if i.val < 192 then
443
else
444)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
392
else
368)
else
(if i.val < 196 then
445
else
384))
else
(if i.val < 199 then
(if i.val < 198 then
446
else
447)
else
(if i.val < 200 then
448
else
(if i.val < 201 then
328
else
416)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
449
else
400)
else
(if i.val < 205 then
450
else
309))
else
(if i.val < 208 then
(if i.val < 207 then
327
else
451)
else
(if i.val < 209 then
452
else
453)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
332
else
359)
else
(if i.val < 213 then
27
else
454))
else
(if i.val < 216 then
(if i.val < 215 then
455
else
422)
else
(if i.val < 217 then
456
else
(if i.val < 218 then
403
else
311)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
457
else
458)
else
(if i.val < 222 then
459
else
47))
else
(if i.val < 225 then
(if i.val < 224 then
460
else
461)
else
(if i.val < 226 then
20
else
29)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
30
else
31)
else
(if i.val < 230 then
44
else
45))
else
(if i.val < 233 then
(if i.val < 232 then
46
else
48)
else
(if i.val < 234 then
49
else
(if i.val < 235 then
50
else
51))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
52
else
53)
else
(if i.val < 239 then
462
else
463))
else
(if i.val < 242 then
(if i.val < 241 then
464
else
465)
else
(if i.val < 243 then
466
else
387)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
314
else
467)
else
(if i.val < 247 then
336
else
366))
else
(if i.val < 250 then
(if i.val < 249 then
391
else
414)
else
(if i.val < 251 then
468
else
(if i.val < 252 then
469
else
470)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
471
else
472)
else
(if i.val < 256 then
398
else
473))
else
(if i.val < 259 then
(if i.val < 258 then
323
else
396)
else
(if i.val < 260 then
420
else
407)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
413
else
340)
else
(if i.val < 264 then
408
else
474))
else
(if i.val < 267 then
(if i.val < 266 then
475
else
476)
else
(if i.val < 268 then
383
else
(if i.val < 269 then
477
else
478)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
395
else
385)
else
(if i.val < 273 then
479
else
480))
else
(if i.val < 276 then
(if i.val < 275 then
481
else
329)
else
(if i.val < 277 then
482
else
483)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
386
else
484)
else
(if i.val < 281 then
485
else
486))
else
(if i.val < 284 then
(if i.val < 283 then
390
else
487)
else
(if i.val < 285 then
488
else
489))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
490
else
418)
else
(if i.val < 289 then
308
else
322))
else
(if i.val < 292 then
(if i.val < 291 then
491
else
360)
else
(if i.val < 293 then
492
else
370)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
372
else
68)
else
(if i.val < 297 then
537
else
61))
else
(if i.val < 300 then
(if i.val < 299 then
114
else
617)
else
(if i.val < 301 then
621
else
(if i.val < 302 then
622
else
56))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
551
else
73)
else
(if i.val < 306 then
538
else
552))
else
(if i.val < 309 then
(if i.val < 308 then
553
else
554)
else
(if i.val < 310 then
111
else
700)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
79
else
573)
else
(if i.val < 314 then
729
else
121))
else
(if i.val < 317 then
(if i.val < 316 then
649
else
619)
else
(if i.val < 318 then
730
else
(if i.val < 319 then
648
else
615)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
620
else
60)
else
(if i.val < 323 then
630
else
137))
else
(if i.val < 326 then
(if i.val < 325 then
698
else
731)
else
(if i.val < 327 then
732
else
694)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
651
else
733)
else
(if i.val < 331 then
734
else
626))
else
(if i.val < 334 then
(if i.val < 333 then
633
else
593)
else
(if i.val < 335 then
570
else
(if i.val < 336 then
708
else
123)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
597
else
604)
else
(if i.val < 340 then
555
else
569))
else
(if i.val < 343 then
(if i.val < 342 then
679
else
735)
else
(if i.val < 344 then
608
else
574)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
69
else
71)
else
(if i.val < 348 then
74
else
75))
else
(if i.val < 351 then
(if i.val < 350 then
76
else
623)
else
(if i.val < 352 then
624
else
(if i.val < 353 then
557
else
625)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
627
else
127)
else
(if i.val < 357 then
545
else
628))
else
(if i.val < 360 then
(if i.val < 359 then
629
else
57)
else
(if i.val < 361 then
539
else
540)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
541
else
542)
else
(if i.val < 365 then
543
else
544))
else
(if i.val < 368 then
(if i.val < 367 then
124
else
546)
else
(if i.val < 369 then
547
else
(if i.val < 370 then
548
else
549))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
550
else
631)
else
(if i.val < 374 then
632
else
634))
else
(if i.val < 377 then
(if i.val < 376 then
635
else
636)
else
(if i.val < 378 then
584
else
560)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
637
else
576)
else
(if i.val < 382 then
638
else
639))
else
(if i.val < 385 then
(if i.val < 384 then
640
else
641)
else
(if i.val < 386 then
592
else
(if i.val < 387 then
642
else
120)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
643
else
644)
else
(if i.val < 391 then
645
else
125))
else
(if i.val < 394 then
(if i.val < 393 then
663
else
736)
else
(if i.val < 395 then
726
else
737)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
579
else
738)
else
(if i.val < 399 then
135
else
685))
else
(if i.val < 402 then
(if i.val < 401 then
739
else
740)
else
(if i.val < 403 then
658
else
(if i.val < 404 then
78
else
715))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
668
else
709)
else
(if i.val < 408 then
741
else
693))
else
(if i.val < 411 then
(if i.val < 410 then
571
else
618)
else
(if i.val < 412 then
680
else
742)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
743
else
126)
else
(if i.val < 416 then
599
else
744))
else
(if i.val < 419 then
(if i.val < 418 then
745
else
725)
else
(if i.val < 420 then
710
else
690))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
603
else
64)
else
(if i.val < 424 then
565
else
591))
else
(if i.val < 427 then
(if i.val < 426 then
646
else
723)
else
(if i.val < 428 then
652
else
746)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
647
else
614)
else
(if i.val < 432 then
132
else
670))
else
(if i.val < 435 then
(if i.val < 434 then
561
else
706)
else
(if i.val < 436 then
747
else
(if i.val < 437 then
748
else
707))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
699
else
749)
else
(if i.val < 441 then
112
else
750))
else
(if i.val < 444 then
(if i.val < 443 then
687
else
712)
else
(if i.val < 445 then
751
else
752)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
81
else
116)
else
(if i.val < 449 then
677
else
753))
else
(if i.val < 452 then
(if i.val < 451 then
754
else
609)
else
(if i.val < 453 then
666
else
(if i.val < 454 then
128
else
62)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
63
else
77)
else
(if i.val < 458 then
80
else
82))
else
(if i.val < 461 then
(if i.val < 460 then
83
else
85)
else
(if i.val < 462 then
86
else
113)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
115
else
117)
else
(if i.val < 466 then
118
else
119))
else
(if i.val < 469 then
(if i.val < 468 then
122
else
129)
else
(if i.val < 470 then
130
else
(if i.val < 471 then
131
else
133)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
134
else
136)
else
(if i.val < 475 then
755
else
683))
else
(if i.val < 478 then
(if i.val < 477 then
661
else
568)
else
(if i.val < 479 then
556
else
717)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
678
else
756)
else
(if i.val < 483 then
692
else
610))
else
(if i.val < 486 then
(if i.val < 485 then
757
else
713)
else
(if i.val < 487 then
586
else
(if i.val < 488 then
714
else
758)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
759
else
760)
else
(if i.val < 492 then
718
else
674))
else
(if i.val < 495 then
(if i.val < 494 then
721
else
684)
else
(if i.val < 496 then
761
else
711)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
762
else
763)
else
(if i.val < 500 then
703
else
686))
else
(if i.val < 503 then
(if i.val < 502 then
722
else
588)
else
(if i.val < 504 then
764
else
(if i.val < 505 then
765
else
697))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
766
else
655)
else
(if i.val < 509 then
595
else
696))
else
(if i.val < 512 then
(if i.val < 511 then
767
else
768)
else
(if i.val < 513 then
598
else
578)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
558
else
563)
else
(if i.val < 517 then
582
else
769))
else
(if i.val < 520 then
(if i.val < 519 then
770
else
771)
else
(if i.val < 521 then
716
else
(if i.val < 522 then
575
else
664)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
605
else
567)
else
(if i.val < 526 then
772
else
773))
else
(if i.val < 529 then
(if i.val < 528 then
774
else
720)
else
(if i.val < 530 then
616
else
775)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
776
else
681)
else
(if i.val < 534 then
777
else
672))
else
(if i.val < 537 then
(if i.val < 536 then
778
else
779)
else
(if i.val < 538 then
169
else
(if i.val < 539 then
187
else
291))))))))))
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
795
else
796)
else
(if i.val < 543 then
184
else
874))
else
(if i.val < 546 then
(if i.val < 545 then
152
else
181)
else
(if i.val < 547 then
903
else
194)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
823
else
293)
else
(if i.val < 551 then
904
else
142))
else
(if i.val < 554 then
(if i.val < 553 then
820
else
821)
else
(if i.val < 555 then
288
else
822))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
269
else
177)
else
(if i.val < 559 then
812
else
824))
else
(if i.val < 562 then
(if i.val < 561 then
825
else
153)
else
(if i.val < 563 then
826
else
827)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
920
else
873)
else
(if i.val < 567 then
940
else
955))
else
(if i.val < 570 then
(if i.val < 569 then
268
else
262)
else
(if i.val < 571 then
156
else
(if i.val < 572 then
969
else
834))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
880
else
924)
else
(if i.val < 576 then
914
else
908))
else
(if i.val < 579 then
(if i.val < 578 then
842
else
916)
else
(if i.val < 580 then
258
else
888)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
970
else
918)
else
(if i.val < 584 then
813
else
868))
else
(if i.val < 587 then
(if i.val < 586 then
965
else
281)
else
(if i.val < 588 then
889
else
(if i.val < 589 then
837
else
949)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
818
else
947)
else
(if i.val < 593 then
271
else
887))
else
(if i.val < 596 then
(if i.val < 595 then
925
else
798)
else
(if i.val < 597 then
931
else
968)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
971
else
900)
else
(if i.val < 601 then
912
else
833))
else
(if i.val < 604 then
(if i.val < 603 then
858
else
951)
else
(if i.val < 605 then
879
else
(if i.val < 606 then
911
else
814)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
846
else
882)
else
(if i.val < 610 then
207
else
277))
else
(if i.val < 613 then
(if i.val < 612 then
898
else
910)
else
(if i.val < 614 then
849
else
149)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
829
else
841)
else
(if i.val < 618 then
172
else
860))
else
(if i.val < 621 then
(if i.val < 620 then
922
else
972)
else
(if i.val < 622 then
173
else
(if i.val < 623 then
174
else
175)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
176
else
157)
else
(if i.val < 627 then
178
else
179))
else
(if i.val < 630 then
(if i.val < 629 then
182
else
183)
else
(if i.val < 631 then
289
else
294)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
804
else
210)
else
(if i.val < 635 then
872
else
905))
else
(if i.val < 638 then
(if i.val < 637 then
906
else
907)
else
(if i.val < 639 then
800
else
(if i.val < 640 then
807
else
267))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
196
else
278)
else
(if i.val < 644 then
853
else
909))
else
(if i.val < 647 then
(if i.val < 646 then
282
else
147)
else
(if i.val < 648 then
148
else
797)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
799
else
801)
else
(if i.val < 652 then
200
else
802))
else
(if i.val < 655 then
(if i.val < 654 then
803
else
805)
else
(if i.val < 656 then
806
else
(if i.val < 657 then
808
else
809)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
810
else
811)
else
(if i.val < 661 then
815
else
266))
else
(if i.val < 664 then
(if i.val < 663 then
816
else
193)
else
(if i.val < 665 then
817
else
819)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
208
else
859)
else
(if i.val < 669 then
913
else
832))
else
(if i.val < 672 then
(if i.val < 671 then
151
else
883)
else
(if i.val < 673 then
915
else
(if i.val < 674 then
867
else
292))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
854
else
917)
else
(if i.val < 678 then
199
else
273))
else
(if i.val < 681 then
(if i.val < 680 then
919
else
899)
else
(if i.val < 682 then
884
else
864)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
265
else
897)
else
(if i.val < 686 then
892
else
950))
else
(if i.val < 689 then
(if i.val < 688 then
190
else
957)
else
(if i.val < 690 then
952
else
259))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
875
else
276)
else
(if i.val < 694 then
263
else
206))
else
(if i.val < 697 then
(if i.val < 696 then
936
else
877)
else
(if i.val < 698 then
871
else
935)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
185
else
844)
else
(if i.val < 702 then
942
else
902))
else
(if i.val < 705 then
(if i.val < 704 then
958
else
845)
else
(if i.val < 706 then
836
else
(if i.val < 707 then
154
else
159))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
839
else
946)
else
(if i.val < 711 then
960
else
973))
else
(if i.val < 714 then
(if i.val < 713 then
191
else
280)
else
(if i.val < 715 then
283
else
850)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
831
else
272)
else
(if i.val < 719 then
290
else
885))
else
(if i.val < 722 then
(if i.val < 721 then
894
else
857)
else
(if i.val < 723 then
930
else
(if i.val < 724 then
866
else
944)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
287
else
959)
else
(if i.val < 728 then
974
else
975))
else
(if i.val < 731 then
(if i.val < 730 then
921
else
881)
else
(if i.val < 732 then
890
else
843)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
275
else
927)
else
(if i.val < 736 then
929
else
937))
else
(if i.val < 739 then
(if i.val < 738 then
270
else
896)
else
(if i.val < 740 then
203
else
(if i.val < 741 then
851
else
260)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
928
else
261)
else
(if i.val < 745 then
201
else
838))
else
(if i.val < 748 then
(if i.val < 747 then
923
else
155)
else
(if i.val < 749 then
158
else
186)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
189
else
192)
else
(if i.val < 753 then
195
else
202))
else
(if i.val < 756 then
(if i.val < 755 then
204
else
264)
else
(if i.val < 757 then
274
else
(if i.val < 758 then
279
else
284)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
285
else
286)
else
(if i.val < 762 then
830
else
901))
else
(if i.val < 765 then
(if i.val < 764 then
934
else
863)
else
(if i.val < 766 then
865
else
861)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
962
else
939)
else
(if i.val < 770 then
891
else
933))
else
(if i.val < 773 then
(if i.val < 772 then
948
else
878)
else
(if i.val < 774 then
895
else
(if i.val < 775 then
862
else
847))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
848
else
932)
else
(if i.val < 779 then
963
else
941))
else
(if i.val < 782 then
(if i.val < 781 then
855
else
886)
else
(if i.val < 783 then
953
else
945)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
976
else
852)
else
(if i.val < 787 then
954
else
876))
else
(if i.val < 790 then
(if i.val < 789 then
956
else
938)
else
(if i.val < 791 then
977
else
(if i.val < 792 then
856
else
964)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
966
else
835)
else
(if i.val < 796 then
361
else
362))
else
(if i.val < 799 then
(if i.val < 798 then
318
else
508)
else
(if i.val < 800 then
315
else
381)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
984
else
427)
else
(if i.val < 804 then
985
else
373))
else
(if i.val < 807 then
(if i.val < 806 then
1001
else
507)
else
(if i.val < 808 then
382
else
(if i.val < 809 then
1021
else
1036)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
402
else
1050)
else
(if i.val < 813 then
514
else
1005))
else
(if i.val < 816 then
(if i.val < 815 then
995
else
989)
else
(if i.val < 817 then
997
else
522)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
1051
else
999)
else
(if i.val < 821 then
306
else
307))
else
(if i.val < 824 then
(if i.val < 823 then
339
else
369)
else
(if i.val < 825 then
1002
else
378))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
1003
else
515)
else
(if i.val < 829 then
1004
else
319))
else
(if i.val < 832 then
(if i.val < 831 then
495
else
520)
else
(if i.val < 833 then
1006
else
1007)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
1008
else
994)
else
(if i.val < 837 then
1009
else
502))
else
(if i.val < 840 then
(if i.val < 839 then
417
else
335)
else
(if i.val < 841 then
990
else
(if i.val < 842 then
529
else
1049))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
326
else
310)
else
(if i.val < 846 then
1024
else
1040))
else
(if i.val < 849 then
(if i.val < 848 then
530
else
531)
else
(if i.val < 850 then
1013
else
404)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
401
else
996)
else
(if i.val < 854 then
388
else
1032))
else
(if i.val < 857 then
(if i.val < 856 then
1025
else
1018)
else
(if i.val < 858 then
493
else
(if i.val < 859 then
1031
else
1028)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
410
else
506)
else
(if i.val < 863 then
527
else
503))
else
(if i.val < 866 then
(if i.val < 865 then
991
else
504)
else
(if i.val < 867 then
426
else
993)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
377
else
1044)
else
(if i.val < 871 then
1023
else
505))
else
(if i.val < 874 then
(if i.val < 873 then
374
else
423)
else
(if i.val < 875 then
364
else
(if i.val < 876 then
1057
else
1034)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
509
else
525)
else
(if i.val < 880 then
338
else
312))
else
(if i.val < 883 then
(if i.val < 882 then
317
else
343)
else
(if i.val < 884 then
1052
else
532)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
1038
else
986)
else
(if i.val < 888 then
333
else
1000))
else
(if i.val < 891 then
(if i.val < 890 then
1012
else
325)
else
(if i.val < 892 then
517
else
(if i.val < 893 then
399
else
1026)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
528
else
526)
else
(if i.val < 897 then
397
else
494))
else
(if i.val < 900 then
(if i.val < 899 then
1035
else
411)
else
(if i.val < 901 then
415
else
497)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
1037
else
367)
else
(if i.val < 905 then
371
else
375))
else
(if i.val < 908 then
(if i.val < 907 then
376
else
379)
else
(if i.val < 909 then
380
else
(if i.val < 910 then
389
else
1046))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
523
else
1030)
else
(if i.val < 914 then
405
else
521))
else
(if i.val < 917 then
(if i.val < 916 then
534
else
513)
else
(if i.val < 918 then
992
else
516)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
341
else
1053)
else
(if i.val < 922 then
313
else
316))
else
(if i.val < 925 then
(if i.val < 924 then
428
else
344)
else
(if i.val < 926 then
987
else
(if i.val < 927 then
988
else
330)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
412
else
342)
else
(if i.val < 931 then
501
else
998))
else
(if i.val < 934 then
(if i.val < 933 then
533
else
518)
else
(if i.val < 935 then
498
else
324)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1033
else
393)
else
(if i.val < 939 then
1017
else
511))
else
(if i.val < 942 then
(if i.val < 941 then
1016
else
536)
else
(if i.val < 943 then
1039
else
(if i.val < 944 then
1027
else
1041))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
1054
else
406)
else
(if i.val < 948 then
424
else
519))
else
(if i.val < 951 then
(if i.val < 950 then
1011
else
500)
else
(if i.val < 952 then
421
else
1055)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
1056
else
1014)
else
(if i.val < 956 then
524
else
1042))
else
(if i.val < 959 then
(if i.val < 958 then
1059
else
499)
else
(if i.val < 960 then
394
else
419))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
1022
else
510)
else
(if i.val < 964 then
535
else
1063))
else
(if i.val < 967 then
(if i.val < 966 then
1015
else
1064)
else
(if i.val < 968 then
1060
else
337)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
409
else
1010)
else
(if i.val < 972 then
512
else
320))
else
(if i.val < 975 then
(if i.val < 974 then
496
else
1019)
else
(if i.val < 976 then
1043
else
(if i.val < 977 then
1020
else
1062))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
1029
else
1045)
else
(if i.val < 981 then
1061
else
1047))
else
(if i.val < 984 then
(if i.val < 983 then
1048
else
1058)
else
(if i.val < 985 then
650
else
653)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
781
else
594)
else
(if i.val < 989 then
1065
else
660))
else
(if i.val < 992 then
(if i.val < 991 then
1066
else
682)
else
(if i.val < 993 then
676
else
(if i.val < 994 then
673
else
794)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
606
else
785)
else
(if i.val < 998 then
662
else
596))
else
(if i.val < 1001 then
(if i.val < 1000 then
665
else
580)
else
(if i.val < 1002 then
654
else
559)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
562
else
1068)
else
(if i.val < 1006 then
583
else
669))
else
(if i.val < 1009 then
(if i.val < 1008 then
601
else
572)
else
(if i.val < 1010 then
705
else
(if i.val < 1011 then
581
else
589)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
587
else
613)
else
(if i.val < 1015 then
786
else
585))
else
(if i.val < 1018 then
(if i.val < 1017 then
566
else
789)
else
(if i.val < 1019 then
791
else
727)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
784
else
656)
else
(if i.val < 1023 then
1071
else
1072))
else
(if i.val < 1026 then
(if i.val < 1025 then
704
else
780)
else
(if i.val < 1027 then
1074
else
(if i.val < 1028 then
1067
else
667)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
1069
else
600)
else
(if i.val < 1032 then
602
else
675))
else
(if i.val < 1035 then
(if i.val < 1034 then
695
else
787)
else
(if i.val < 1036 then
611
else
657)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
702
else
719)
else
(if i.val < 1040 then
701
else
607))
else
(if i.val < 1043 then
(if i.val < 1042 then
724
else
788)
else
(if i.val < 1044 then
728
else
(if i.val < 1045 then
1070
else
1079))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
612
else
1075)
else
(if i.val < 1049 then
1077
else
577))
else
(if i.val < 1052 then
(if i.val < 1051 then
659
else
590)
else
(if i.val < 1053 then
671
else
564)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
783
else
689)
else
(if i.val < 1057 then
782
else
691))
else
(if i.val < 1060 then
(if i.val < 1059 then
1078
else
688)
else
(if i.val < 1061 then
1073
else
(if i.val < 1062 then
1076
else
790)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
792
else
793)
else
(if i.val < 1066 then
926
else
840))
else
(if i.val < 1069 then
(if i.val < 1068 then
943
else
828)
else
(if i.val < 1070 then
978
else
869)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
961
else
870)
else
(if i.val < 1074 then
967
else
893))
else
(if i.val < 1077 then
(if i.val < 1076 then
981
else
980)
else
(if i.val < 1078 then
982
else
(if i.val < 1079 then
983
else
979)))))))))))

def g32p_row06_cosetGeneratorNextColumn2 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
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
43)
else
(if i.val < 11 then
44
else
38))
else
(if i.val < 14 then
(if i.val < 13 then
45
else
31)
else
(if i.val < 15 then
0
else
46))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
47
else
48)
else
(if i.val < 19 then
19
else
59))
else
(if i.val < 22 then
(if i.val < 21 then
60
else
61)
else
(if i.val < 23 then
76
else
77)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
71
else
78)
else
(if i.val < 27 then
64
else
1))
else
(if i.val < 30 then
(if i.val < 29 then
79
else
80)
else
(if i.val < 31 then
81
else
(if i.val < 32 then
2
else
111))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
101
else
112)
else
(if i.val < 36 then
113
else
114))
else
(if i.val < 39 then
(if i.val < 38 then
115
else
102)
else
(if i.val < 40 then
72
else
103)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
116
else
117)
else
(if i.val < 44 then
118
else
119))
else
(if i.val < 47 then
(if i.val < 46 then
120
else
4)
else
(if i.val < 48 then
121
else
(if i.val < 49 then
122
else
123)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
124
else
125)
else
(if i.val < 53 then
126
else
127))
else
(if i.val < 56 then
(if i.val < 55 then
128
else
149)
else
(if i.val < 57 then
150
else
144)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
151
else
18)
else
(if i.val < 61 then
5
else
152))
else
(if i.val < 64 then
(if i.val < 63 then
153
else
154)
else
(if i.val < 65 then
6
else
(if i.val < 66 then
184
else
174)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
185
else
186)
else
(if i.val < 70 then
187
else
188))
else
(if i.val < 73 then
(if i.val < 72 then
175
else
145)
else
(if i.val < 74 then
176
else
189)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
190
else
191)
else
(if i.val < 78 then
192
else
193))
else
(if i.val < 81 then
(if i.val < 80 then
8
else
194)
else
(if i.val < 82 then
195
else
(if i.val < 83 then
196
else
197)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
198
else
199)
else
(if i.val < 87 then
200
else
201))
else
(if i.val < 90 then
(if i.val < 89 then
241
else
205)
else
(if i.val < 91 then
258
else
167)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
259
else
260)
else
(if i.val < 95 then
229
else
261))
else
(if i.val < 98 then
(if i.val < 97 then
168
else
262)
else
(if i.val < 99 then
228
else
(if i.val < 100 then
263
else
264))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
238
else
11)
else
(if i.val < 104 then
239
else
230))
else
(if i.val < 107 then
(if i.val < 106 then
240
else
265)
else
(if i.val < 108 then
266
else
267)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
214
else
203)
else
(if i.val < 112 then
268
else
269))
else
(if i.val < 115 then
(if i.val < 114 then
270
else
242)
else
(if i.val < 116 then
206
else
(if i.val < 117 then
271
else
272)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
9
else
10)
else
(if i.val < 121 then
12
else
16))
else
(if i.val < 124 then
(if i.val < 123 then
17
else
221)
else
(if i.val < 125 then
273
else
274)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
275
else
276)
else
(if i.val < 129 then
252
else
166))
else
(if i.val < 132 then
(if i.val < 131 then
277
else
278)
else
(if i.val < 133 then
279
else
(if i.val < 134 then
143
else
280))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
281
else
282)
else
(if i.val < 138 then
283
else
318))
else
(if i.val < 141 then
(if i.val < 140 then
308
else
319)
else
(if i.val < 142 then
320
else
321)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
322
else
309)
else
(if i.val < 146 then
39
else
310))
else
(if i.val < 149 then
(if i.val < 148 then
323
else
324)
else
(if i.val < 150 then
325
else
326))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
327
else
21)
else
(if i.val < 154 then
328
else
329))
else
(if i.val < 157 then
(if i.val < 156 then
330
else
331)
else
(if i.val < 158 then
332
else
333)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
334
else
335)
else
(if i.val < 162 then
375
else
339))
else
(if i.val < 165 then
(if i.val < 164 then
392
else
301)
else
(if i.val < 166 then
393
else
(if i.val < 167 then
394
else
363))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
395
else
302)
else
(if i.val < 171 then
396
else
362))
else
(if i.val < 174 then
(if i.val < 173 then
397
else
398)
else
(if i.val < 175 then
372
else
24)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
373
else
364)
else
(if i.val < 179 then
374
else
399))
else
(if i.val < 182 then
(if i.val < 181 then
400
else
401)
else
(if i.val < 183 then
348
else
(if i.val < 184 then
337
else
402)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
403
else
404)
else
(if i.val < 188 then
376
else
340))
else
(if i.val < 191 then
(if i.val < 190 then
405
else
406)
else
(if i.val < 192 then
22
else
23)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
25
else
29)
else
(if i.val < 196 then
30
else
355))
else
(if i.val < 199 then
(if i.val < 198 then
407
else
408)
else
(if i.val < 200 then
409
else
(if i.val < 201 then
410
else
386)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
300
else
411)
else
(if i.val < 205 then
412
else
413))
else
(if i.val < 208 then
(if i.val < 207 then
37
else
414)
else
(if i.val < 209 then
415
else
416)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
417
else
477)
else
(if i.val < 213 then
465
else
493))
else
(if i.val < 216 then
(if i.val < 215 then
494
else
349)
else
(if i.val < 217 then
430
else
(if i.val < 218 then
438
else
440)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
420
else
482)
else
(if i.val < 222 then
49
else
389))
else
(if i.val < 225 then
(if i.val < 224 then
495
else
454)
else
(if i.val < 226 then
359
else
496)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
459
else
466)
else
(if i.val < 230 then
298
else
432))
else
(if i.val < 233 then
(if i.val < 232 then
387
else
497)
else
(if i.val < 234 then
445
else
(if i.val < 235 then
498
else
429))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
344
else
499)
else
(if i.val < 239 then
33
else
40))
else
(if i.val < 242 then
(if i.val < 241 then
474
else
462)
else
(if i.val < 243 then
36
else
463)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
447
else
464)
else
(if i.val < 247 then
475
else
476))
else
(if i.val < 250 then
(if i.val < 249 then
383
else
455)
else
(if i.val < 251 then
500
else
(if i.val < 252 then
501
else
54)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
502
else
503)
else
(if i.val < 256 then
504
else
505))
else
(if i.val < 259 then
(if i.val < 258 then
506
else
507)
else
(if i.val < 260 then
435
else
336)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
303
else
508)
else
(if i.val < 264 then
509
else
510))
else
(if i.val < 267 then
(if i.val < 266 then
446
else
511)
else
(if i.val < 268 then
512
else
(if i.val < 269 then
32
else
34)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
35
else
41)
else
(if i.val < 273 then
42
else
50))
else
(if i.val < 276 then
(if i.val < 275 then
51
else
52)
else
(if i.val < 277 then
53
else
317)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
513
else
296)
else
(if i.val < 281 then
514
else
515))
else
(if i.val < 284 then
(if i.val < 283 then
516
else
370)
else
(if i.val < 285 then
517
else
518))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
519
else
357)
else
(if i.val < 289 then
520
else
352))
else
(if i.val < 292 then
(if i.val < 291 then
521
else
522)
else
(if i.val < 293 then
347
else
358)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
523
else
567)
else
(if i.val < 297 then
132
else
584))
else
(if i.val < 300 then
(if i.val < 299 then
94
else
585)
else
(if i.val < 301 then
586
else
(if i.val < 302 then
555
else
587))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
95
else
588)
else
(if i.val < 306 then
554
else
589))
else
(if i.val < 309 then
(if i.val < 308 then
590
else
564)
else
(if i.val < 310 then
57
else
565)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
556
else
566)
else
(if i.val < 314 then
591
else
592))
else
(if i.val < 317 then
(if i.val < 316 then
593
else
540)
else
(if i.val < 318 then
130
else
(if i.val < 319 then
594
else
595)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
596
else
568)
else
(if i.val < 323 then
133
else
597))
else
(if i.val < 326 then
(if i.val < 325 then
598
else
55)
else
(if i.val < 327 then
56
else
58)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
62
else
63)
else
(if i.val < 331 then
547
else
599))
else
(if i.val < 334 then
(if i.val < 333 then
600
else
601)
else
(if i.val < 335 then
602
else
(if i.val < 336 then
578
else
93)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
603
else
604)
else
(if i.val < 340 then
605
else
70))
else
(if i.val < 343 then
(if i.val < 342 then
606
else
607)
else
(if i.val < 344 then
608
else
609)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
669
else
657)
else
(if i.val < 348 then
685
else
686))
else
(if i.val < 351 then
(if i.val < 350 then
541
else
622)
else
(if i.val < 352 then
630
else
(if i.val < 353 then
632
else
612)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
674
else
82)
else
(if i.val < 357 then
581
else
687))
else
(if i.val < 360 then
(if i.val < 359 then
646
else
551)
else
(if i.val < 361 then
688
else
651)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
658
else
91)
else
(if i.val < 365 then
624
else
579))
else
(if i.val < 368 then
(if i.val < 367 then
689
else
637)
else
(if i.val < 369 then
690
else
(if i.val < 370 then
621
else
137))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
691
else
66)
else
(if i.val < 374 then
73
else
666))
else
(if i.val < 377 then
(if i.val < 376 then
654
else
69)
else
(if i.val < 378 then
655
else
639)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
656
else
667)
else
(if i.val < 382 then
668
else
575))
else
(if i.val < 385 then
(if i.val < 384 then
647
else
692)
else
(if i.val < 386 then
693
else
(if i.val < 387 then
87
else
694)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
695
else
696)
else
(if i.val < 391 then
697
else
698))
else
(if i.val < 394 then
(if i.val < 393 then
699
else
627)
else
(if i.val < 395 then
129
else
96)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
700
else
701)
else
(if i.val < 399 then
702
else
638))
else
(if i.val < 402 then
(if i.val < 401 then
703
else
704)
else
(if i.val < 403 then
65
else
(if i.val < 404 then
67
else
68))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
74
else
75)
else
(if i.val < 408 then
83
else
84))
else
(if i.val < 411 then
(if i.val < 410 then
85
else
86)
else
(if i.val < 412 then
110
else
705)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
89
else
706)
else
(if i.val < 416 then
707
else
708))
else
(if i.val < 419 then
(if i.val < 418 then
562
else
709)
else
(if i.val < 420 then
710
else
711))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
549
else
712)
else
(if i.val < 424 then
544
else
713))
else
(if i.val < 427 then
(if i.val < 426 then
714
else
539)
else
(if i.val < 428 then
550
else
715)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
653
else
635)
else
(if i.val < 432 then
620
else
104))
else
(if i.val < 435 then
(if i.val < 434 then
721
else
684)
else
(if i.val < 436 then
92
else
(if i.val < 437 then
772
else
583))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
663
else
648)
else
(if i.val < 441 then
615
else
736))
else
(if i.val < 444 then
(if i.val < 443 then
726
else
542)
else
(if i.val < 445 then
614
else
741)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
106
else
644)
else
(if i.val < 449 then
761
else
563))
else
(if i.val < 452 then
(if i.val < 451 then
665
else
733)
else
(if i.val < 453 then
570
else
(if i.val < 454 then
780
else
619)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
574
else
781)
else
(if i.val < 458 then
782
else
680))
else
(if i.val < 461 then
(if i.val < 460 then
683
else
775)
else
(if i.val < 462 then
561
else
88)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
670
else
762)
else
(if i.val < 466 then
737
else
98))
else
(if i.val < 469 then
(if i.val < 468 then
717
else
628)
else
(if i.val < 470 then
778
else
(if i.val < 471 then
744
else
543)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
783
else
770)
else
(if i.val < 475 then
105
else
752))
else
(if i.val < 478 then
(if i.val < 477 then
763
else
743)
else
(if i.val < 479 then
569
else
755)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
661
else
640)
else
(if i.val < 483 then
739
else
722))
else
(if i.val < 486 then
(if i.val < 485 then
732
else
764)
else
(if i.val < 487 then
765
else
(if i.val < 488 then
766
else
784)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
662
else
740)
else
(if i.val < 492 then
553
else
750))
else
(if i.val < 495 then
(if i.val < 494 then
618
else
109)
else
(if i.val < 496 then
613
else
734)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
767
else
779)
else
(if i.val < 500 then
641
else
725))
else
(if i.val < 503 then
(if i.val < 502 then
735
else
557)
else
(if i.val < 504 then
729
else
(if i.val < 505 then
548
else
759))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
629
else
90)
else
(if i.val < 509 then
97
else
99))
else
(if i.val < 512 then
(if i.val < 511 then
100
else
107)
else
(if i.val < 513 then
108
else
131)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
134
else
135)
else
(if i.val < 517 then
136
else
785))
else
(if i.val < 520 then
(if i.val < 519 then
786
else
545)
else
(if i.val < 521 then
636
else
(if i.val < 522 then
787
else
777)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
623
else
746)
else
(if i.val < 526 then
788
else
633))
else
(if i.val < 529 then
(if i.val < 528 then
652
else
754)
else
(if i.val < 530 then
748
else
789)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
643
else
720)
else
(if i.val < 534 then
576
else
776))
else
(if i.val < 537 then
(if i.val < 536 then
671
else
678)
else
(if i.val < 538 then
843
else
(if i.val < 539 then
831
else
859))))))))))
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
860
else
215)
else
(if i.val < 543 then
796
else
804))
else
(if i.val < 546 then
(if i.val < 545 then
806
else
286)
else
(if i.val < 547 then
848
else
155)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
255
else
861)
else
(if i.val < 551 then
820
else
225))
else
(if i.val < 554 then
(if i.val < 553 then
862
else
825)
else
(if i.val < 555 then
832
else
164))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
798
else
253)
else
(if i.val < 559 then
863
else
811))
else
(if i.val < 562 then
(if i.val < 561 then
864
else
795)
else
(if i.val < 563 then
210
else
865)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
139
else
146)
else
(if i.val < 567 then
840
else
828))
else
(if i.val < 570 then
(if i.val < 569 then
142
else
829)
else
(if i.val < 571 then
813
else
(if i.val < 572 then
830
else
841))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
842
else
249)
else
(if i.val < 576 then
821
else
866))
else
(if i.val < 579 then
(if i.val < 578 then
867
else
160)
else
(if i.val < 580 then
868
else
869)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
870
else
871)
else
(if i.val < 584 then
872
else
873))
else
(if i.val < 587 then
(if i.val < 586 then
801
else
202)
else
(if i.val < 588 then
169
else
(if i.val < 589 then
874
else
875)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
876
else
812)
else
(if i.val < 593 then
877
else
878))
else
(if i.val < 596 then
(if i.val < 595 then
138
else
140)
else
(if i.val < 597 then
141
else
147)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
148
else
156)
else
(if i.val < 601 then
157
else
158))
else
(if i.val < 604 then
(if i.val < 603 then
159
else
183)
else
(if i.val < 605 then
879
else
(if i.val < 606 then
162
else
880)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
881
else
882)
else
(if i.val < 610 then
236
else
883))
else
(if i.val < 613 then
(if i.val < 612 then
884
else
885)
else
(if i.val < 614 then
223
else
886)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
218
else
887)
else
(if i.val < 618 then
888
else
213))
else
(if i.val < 621 then
(if i.val < 620 then
224
else
889)
else
(if i.val < 622 then
827
else
(if i.val < 623 then
809
else
294)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
177
else
895)
else
(if i.val < 627 then
858
else
165))
else
(if i.val < 630 then
(if i.val < 629 then
946
else
257)
else
(if i.val < 631 then
837
else
822)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
289
else
910)
else
(if i.val < 635 then
900
else
216))
else
(if i.val < 638 then
(if i.val < 637 then
288
else
915)
else
(if i.val < 639 then
179
else
(if i.val < 640 then
818
else
935))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
237
else
839)
else
(if i.val < 644 then
907
else
244))
else
(if i.val < 647 then
(if i.val < 646 then
954
else
293)
else
(if i.val < 648 then
248
else
955)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
956
else
854)
else
(if i.val < 652 then
857
else
949))
else
(if i.val < 655 then
(if i.val < 654 then
235
else
161)
else
(if i.val < 656 then
844
else
(if i.val < 657 then
936
else
911)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
171
else
891)
else
(if i.val < 661 then
802
else
952))
else
(if i.val < 664 then
(if i.val < 663 then
918
else
217)
else
(if i.val < 665 then
957
else
944)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
178
else
926)
else
(if i.val < 669 then
937
else
917))
else
(if i.val < 672 then
(if i.val < 671 then
243
else
929)
else
(if i.val < 673 then
835
else
(if i.val < 674 then
814
else
913))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
896
else
906)
else
(if i.val < 678 then
938
else
939))
else
(if i.val < 681 then
(if i.val < 680 then
940
else
958)
else
(if i.val < 682 then
836
else
914)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
227
else
924)
else
(if i.val < 686 then
292
else
182))
else
(if i.val < 689 then
(if i.val < 688 then
287
else
908)
else
(if i.val < 690 then
941
else
953))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
815
else
899)
else
(if i.val < 694 then
909
else
231))
else
(if i.val < 697 then
(if i.val < 696 then
903
else
222)
else
(if i.val < 698 then
933
else
803)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
163
else
170)
else
(if i.val < 702 then
172
else
173))
else
(if i.val < 705 then
(if i.val < 704 then
180
else
181)
else
(if i.val < 706 then
204
else
(if i.val < 707 then
207
else
208))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
209
else
959)
else
(if i.val < 711 then
960
else
219))
else
(if i.val < 714 then
(if i.val < 713 then
810
else
961)
else
(if i.val < 715 then
951
else
797)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
920
else
962)
else
(if i.val < 719 then
807
else
826))
else
(if i.val < 722 then
(if i.val < 721 then
928
else
922)
else
(if i.val < 723 then
963
else
(if i.val < 724 then
817
else
894)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
250
else
950)
else
(if i.val < 728 then
845
else
852))
else
(if i.val < 731 then
(if i.val < 730 then
254
else
930)
else
(if i.val < 732 then
905
else
972)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
897
else
226)
else
(if i.val < 736 then
251
else
892))
else
(if i.val < 739 then
(if i.val < 738 then
212
else
965)
else
(if i.val < 740 then
220
else
(if i.val < 741 then
970
else
233)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
819
else
211)
else
(if i.val < 745 then
855
else
912))
else
(if i.val < 748 then
(if i.val < 747 then
925
else
973)
else
(if i.val < 749 then
799
else
923)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
800
else
890)
else
(if i.val < 753 then
246
else
823))
else
(if i.val < 756 then
(if i.val < 755 then
898
else
901)
else
(if i.val < 757 then
971
else
(if i.val < 758 then
931
else
978)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
256
else
974)
else
(if i.val < 762 then
847
else
245))
else
(if i.val < 765 then
(if i.val < 764 then
247
else
945)
else
(if i.val < 766 then
902
else
968)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
232
else
934)
else
(if i.val < 770 then
976
else
816))
else
(if i.val < 773 then
(if i.val < 772 then
851
else
834)
else
(if i.val < 774 then
838
else
(if i.val < 775 then
943
else
893))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
808
else
291)
else
(if i.val < 779 then
846
else
234))
else
(if i.val < 782 then
(if i.val < 781 then
916
else
805)
else
(if i.val < 783 then
927
else
947)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
824
else
284)
else
(if i.val < 787 then
285
else
290))
else
(if i.val < 790 then
(if i.val < 789 then
833
else
849)
else
(if i.val < 791 then
979
else
(if i.val < 792 then
919
else
980)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
981
else
853)
else
(if i.val < 796 then
461
else
443))
else
(if i.val < 799 then
(if i.val < 798 then
428
else
311)
else
(if i.val < 800 then
529
else
492)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
299
else
1027)
else
(if i.val < 804 then
391
else
471))
else
(if i.val < 807 then
(if i.val < 806 then
456
else
423)
else
(if i.val < 808 then
991
else
(if i.val < 809 then
534
else
350)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
422
else
996)
else
(if i.val < 813 then
313
else
452))
else
(if i.val < 816 then
(if i.val < 815 then
1016
else
371)
else
(if i.val < 817 then
473
else
988)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
378
else
1035)
else
(if i.val < 821 then
427
else
382))
else
(if i.val < 824 then
(if i.val < 823 then
1036
else
1037)
else
(if i.val < 825 then
488
else
491))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
1030
else
369)
else
(if i.val < 829 then
295
else
478))
else
(if i.val < 832 then
(if i.val < 831 then
1017
else
992)
else
(if i.val < 833 then
305
else
525)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
436
else
1033)
else
(if i.val < 837 then
999
else
351))
else
(if i.val < 840 then
(if i.val < 839 then
1038
else
1025)
else
(if i.val < 841 then
312
else
(if i.val < 842 then
1007
else
1018))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
998
else
377)
else
(if i.val < 846 then
1010
else
469))
else
(if i.val < 849 then
(if i.val < 848 then
448
else
994)
else
(if i.val < 850 then
530
else
987)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
1019
else
1020)
else
(if i.val < 854 then
1021
else
1039))
else
(if i.val < 857 then
(if i.val < 856 then
470
else
995)
else
(if i.val < 858 then
361
else
(if i.val < 859 then
1005
else
426)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
316
else
421)
else
(if i.val < 863 then
989
else
1022))
else
(if i.val < 866 then
(if i.val < 865 then
1034
else
449)
else
(if i.val < 867 then
533
else
990)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
365
else
984)
else
(if i.val < 871 then
356
else
1014))
else
(if i.val < 874 then
(if i.val < 873 then
437
else
297)
else
(if i.val < 875 then
304
else
(if i.val < 876 then
306
else
307)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
314
else
315)
else
(if i.val < 880 then
338
else
341))
else
(if i.val < 883 then
(if i.val < 882 then
342
else
343)
else
(if i.val < 884 then
1040
else
1041)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
353
else
444)
else
(if i.val < 888 then
1042
else
1032))
else
(if i.val < 891 then
(if i.val < 890 then
431
else
1001)
else
(if i.val < 892 then
1043
else
(if i.val < 893 then
441
else
460)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
1009
else
1003)
else
(if i.val < 897 then
1044
else
451))
else
(if i.val < 900 then
(if i.val < 899 then
528
else
384)
else
(if i.val < 901 then
1031
else
479)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
486
else
388)
else
(if i.val < 905 then
1011
else
986))
else
(if i.val < 908 then
(if i.val < 907 then
1053
else
531)
else
(if i.val < 909 then
360
else
(if i.val < 910 then
385
else
526))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
346
else
1046)
else
(if i.val < 914 then
354
else
1051))
else
(if i.val < 917 then
(if i.val < 916 then
367
else
453)
else
(if i.val < 918 then
345
else
489)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
993
else
1006)
else
(if i.val < 922 then
1054
else
433))
else
(if i.val < 925 then
(if i.val < 924 then
1004
else
434)
else
(if i.val < 926 then
524
else
(if i.val < 927 then
380
else
457)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
532
else
535)
else
(if i.val < 931 then
1052
else
1012))
else
(if i.val < 934 then
(if i.val < 933 then
1059
else
390)
else
(if i.val < 935 then
1055
else
481)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
379
else
381)
else
(if i.val < 939 then
1026
else
536))
else
(if i.val < 942 then
(if i.val < 941 then
1049
else
366)
else
(if i.val < 943 then
1015
else
(if i.val < 944 then
1057
else
450))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
485
else
468)
else
(if i.val < 948 then
472
else
1024))
else
(if i.val < 951 then
(if i.val < 950 then
527
else
442)
else
(if i.val < 952 then
425
else
480)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
368
else
997)
else
(if i.val < 956 then
439
else
1008))
else
(if i.val < 959 then
(if i.val < 958 then
1028
else
458)
else
(if i.val < 960 then
418
else
419))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
424
else
467)
else
(if i.val < 964 then
483
else
1060))
else
(if i.val < 967 then
(if i.val < 966 then
1000
else
1061)
else
(if i.val < 968 then
1062
else
487)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
1013
else
490)
else
(if i.val < 972 then
985
else
484))
else
(if i.val < 975 then
(if i.val < 974 then
1056
else
1023)
else
(if i.val < 976 then
1002
else
(if i.val < 977 then
1029
else
1047))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
1050
else
1064)
else
(if i.val < 981 then
1058
else
1063))
else
(if i.val < 984 then
(if i.val < 983 then
1048
else
1045)
else
(if i.val < 985 then
580
else
756)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
731
else
1068)
else
(if i.val < 989 then
723
else
552))
else
(if i.val < 992 then
(if i.val < 991 then
577
else
718)
else
(if i.val < 993 then
538
else
(if i.val < 994 then
791
else
546)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
1066
else
559)
else
(if i.val < 998 then
645
else
537))
else
(if i.val < 1001 then
(if i.val < 1000 then
681
else
738)
else
(if i.val < 1002 then
751
else
1069)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
625
else
749)
else
(if i.val < 1006 then
626
else
716))
else
(if i.val < 1009 then
(if i.val < 1008 then
572
else
649)
else
(if i.val < 1010 then
724
else
(if i.val < 1011 then
727
else
1067)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
757
else
1074)
else
(if i.val < 1015 then
582
else
1070))
else
(if i.val < 1018 then
(if i.val < 1017 then
673
else
571)
else
(if i.val < 1019 then
573
else
771)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
728
else
794)
else
(if i.val < 1023 then
558
else
760))
else
(if i.val < 1026 then
(if i.val < 1025 then
1072
else
642)
else
(if i.val < 1027 then
677
else
(if i.val < 1028 then
660
else
664)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
769
else
719)
else
(if i.val < 1032 then
634
else
617))
else
(if i.val < 1035 then
(if i.val < 1034 then
672
else
560)
else
(if i.val < 1036 then
742
else
631)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
753
else
773)
else
(if i.val < 1040 then
650
else
610))
else
(if i.val < 1043 then
(if i.val < 1042 then
611
else
616)
else
(if i.val < 1044 then
659
else
(if i.val < 1045 then
675
else
1075))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
745
else
1076)
else
(if i.val < 1049 then
1077
else
679))
else
(if i.val < 1052 then
(if i.val < 1051 then
758
else
682)
else
(if i.val < 1053 then
730
else
676)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
1071
else
768)
else
(if i.val < 1057 then
747
else
774))
else
(if i.val < 1060 then
(if i.val < 1059 then
792
else
1065)
else
(if i.val < 1061 then
1079
else
(if i.val < 1062 then
1073
else
1078)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
793
else
790)
else
(if i.val < 1066 then
932
else
856))
else
(if i.val < 1069 then
(if i.val < 1068 then
904
else
850)
else
(if i.val < 1070 then
975
else
942)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
921
else
948)
else
(if i.val < 1074 then
966
else
969))
else
(if i.val < 1077 then
(if i.val < 1076 then
983
else
977)
else
(if i.val < 1078 then
982
else
(if i.val < 1079 then
967
else
964)))))))))))

def g32p_row06_cosetGeneratorNextColumn3 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
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
49)
else
(if i.val < 7 then
50
else
24)))
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
51)
else
(if i.val < 15 then
52
else
48))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
53
else
54)
else
(if i.val < 19 then
0
else
122))
else
(if i.val < 22 then
(if i.val < 21 then
129
else
130)
else
(if i.val < 23 then
107
else
77)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
69
else
83)
else
(if i.val < 27 then
91
else
131))
else
(if i.val < 30 then
(if i.val < 29 then
132
else
82)
else
(if i.val < 31 then
57
else
(if i.val < 32 then
62
else
106))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
66
else
92)
else
(if i.val < 36 then
99
else
100))
else
(if i.val < 39 then
(if i.val < 38 then
101
else
108)
else
(if i.val < 40 then
109
else
105)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
110
else
87)
else
(if i.val < 44 then
2
else
133))
else
(if i.val < 47 then
(if i.val < 46 then
125
else
134)
else
(if i.val < 48 then
71
else
(if i.val < 49 then
126
else
135)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
136
else
116)
else
(if i.val < 53 then
137
else
1))
else
(if i.val < 56 then
(if i.val < 55 then
3
else
216)
else
(if i.val < 57 then
238
else
202)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
232
else
252)
else
(if i.val < 61 then
261
else
284))
else
(if i.val < 64 then
(if i.val < 63 then
203
else
148)
else
(if i.val < 65 then
159
else
(if i.val < 66 then
234
else
139)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
221
else
285)
else
(if i.val < 70 then
7
else
150))
else
(if i.val < 73 then
(if i.val < 72 then
278
else
235)
else
(if i.val < 74 then
262
else
180)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
142
else
156)
else
(if i.val < 78 then
192
else
144))
else
(if i.val < 81 then
(if i.val < 80 then
286
else
279)
else
(if i.val < 82 then
205
else
(if i.val < 83 then
8
else
195)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
164
else
204)
else
(if i.val < 87 then
155
else
11))
else
(if i.val < 90 then
(if i.val < 89 then
245
else
250)
else
(if i.val < 91 then
251
else
171)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
220
else
211)
else
(if i.val < 95 then
213
else
233))
else
(if i.val < 98 then
(if i.val < 97 then
162
else
226)
else
(if i.val < 99 then
236
else
(if i.val < 100 then
237
else
160))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
10
else
253)
else
(if i.val < 104 then
248
else
254))
else
(if i.val < 107 then
(if i.val < 106 then
249
else
255)
else
(if i.val < 108 then
256
else
198)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
257
else
9)
else
(if i.val < 112 then
287
else
288))
else
(if i.val < 115 then
(if i.val < 114 then
289
else
290)
else
(if i.val < 116 then
143
else
(if i.val < 117 then
13
else
267)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
274
else
188)
else
(if i.val < 121 then
291
else
292))
else
(if i.val < 124 then
(if i.val < 123 then
280
else
166)
else
(if i.val < 125 then
167
else
153)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
15
else
175)
else
(if i.val < 129 then
275
else
173))
else
(if i.val < 132 then
(if i.val < 131 then
208
else
293)
else
(if i.val < 133 then
294
else
(if i.val < 134 then
174
else
283))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
5
else
6)
else
(if i.val < 138 then
14
else
489))
else
(if i.val < 141 then
(if i.val < 140 then
33
else
431)
else
(if i.val < 142 then
462
else
336)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
340
else
413)
else
(if i.val < 146 then
491
else
469))
else
(if i.val < 149 then
(if i.val < 148 then
482
else
307)
else
(if i.val < 150 then
343
else
372))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
315
else
524)
else
(if i.val < 154 then
45
else
525))
else
(if i.val < 157 then
(if i.val < 156 then
337
else
366)
else
(if i.val < 158 then
526
else
527)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
342
else
36)
else
(if i.val < 162 then
456
else
345))
else
(if i.val < 165 then
(if i.val < 164 then
459
else
386)
else
(if i.val < 166 then
355
else
(if i.val < 167 then
303
else
334))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
467
else
528)
else
(if i.val < 171 then
488
else
26))
else
(if i.val < 174 then
(if i.val < 173 then
419
else
20)
else
(if i.val < 175 then
44
else
347)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
529
else
530)
else
(if i.val < 179 then
396
else
368))
else
(if i.val < 182 then
(if i.val < 181 then
350
else
412)
else
(if i.val < 183 then
369
else
(if i.val < 184 then
314
else
531)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
515
else
367)
else
(if i.val < 188 then
513
else
308))
else
(if i.val < 191 then
(if i.val < 190 then
298
else
477)
else
(if i.val < 192 then
365
else
23)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
500
else
532)
else
(if i.val < 196 then
25
else
296))
else
(if i.val < 199 then
(if i.val < 198 then
309
else
38)
else
(if i.val < 200 then
339
else
(if i.val < 201 then
533
else
512)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
30
else
31)
else
(if i.val < 205 then
395
else
418))
else
(if i.val < 208 then
(if i.val < 207 then
326
else
420)
else
(if i.val < 209 then
21
else
329)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
338
else
449)
else
(if i.val < 213 then
470
else
400))
else
(if i.val < 216 then
(if i.val < 215 then
429
else
437)
else
(if i.val < 217 then
444
else
(if i.val < 218 then
321
else
490)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
484
else
34)
else
(if i.val < 222 then
445
else
346))
else
(if i.val < 225 then
(if i.val < 224 then
450
else
435)
else
(if i.val < 226 then
468
else
458)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
359
else
454)
else
(if i.val < 230 then
471
else
391))
else
(if i.val < 233 then
(if i.val < 232 then
472
else
414)
else
(if i.val < 234 then
398
else
(if i.val < 235 then
473
else
447))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
323
else
35)
else
(if i.val < 239 then
322
else
304))
else
(if i.val < 242 then
(if i.val < 241 then
383
else
481)
else
(if i.val < 243 then
440
else
360)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
492
else
485)
else
(if i.val < 247 then
348
else
349))
else
(if i.val < 250 then
(if i.val < 249 then
433
else
40)
else
(if i.val < 251 then
300
else
(if i.val < 252 then
452
else
370)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
301
else
487)
else
(if i.val < 256 then
32
else
22))
else
(if i.val < 259 then
(if i.val < 258 then
39
else
476)
else
(if i.val < 260 then
520
else
486)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
403
else
463)
else
(if i.val < 264 then
352
else
521))
else
(if i.val < 267 then
(if i.val < 266 then
357
else
331)
else
(if i.val < 268 then
502
else
(if i.val < 269 then
504
else
344)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
460
else
328)
else
(if i.val < 273 then
448
else
534))
else
(if i.val < 276 then
(if i.val < 275 then
522
else
514)
else
(if i.val < 277 then
376
else
517)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
47
else
519)
else
(if i.val < 281 then
19
else
394))
else
(if i.val < 284 then
(if i.val < 283 then
363
else
46)
else
(if i.val < 285 then
535
else
536))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
393
else
446)
else
(if i.val < 289 then
466
else
302))
else
(if i.val < 292 then
(if i.val < 291 then
441
else
411)
else
(if i.val < 293 then
358
else
27)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
28
else
759)
else
(if i.val < 297 then
720
else
758))
else
(if i.val < 300 then
(if i.val < 299 then
718
else
710)
else
(if i.val < 301 then
89
else
(if i.val < 302 then
102
else
113))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
123
else
569)
else
(if i.val < 306 then
578
else
703))
else
(if i.val < 309 then
(if i.val < 308 then
63
else
119)
else
(if i.val < 310 then
725
else
700)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
760
else
566)
else
(if i.val < 314 then
790
else
674))
else
(if i.val < 317 then
(if i.val < 316 then
711
else
556)
else
(if i.val < 318 then
582
else
(if i.val < 319 then
770
else
755)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
762
else
743)
else
(if i.val < 323 then
56
else
98))
else
(if i.val < 326 then
(if i.val < 325 then
788
else
673)
else
(if i.val < 327 then
564
else
732)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
777
else
558)
else
(if i.val < 331 then
576
else
579))
else
(if i.val < 334 then
(if i.val < 333 then
604
else
620)
else
(if i.val < 335 then
124
else
(if i.val < 336 then
787
else
75)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
86
else
719)
else
(if i.val < 340 then
717
else
115))
else
(if i.val < 343 then
(if i.val < 342 then
738
else
64)
else
(if i.val < 344 then
606
else
619)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
96
else
642)
else
(if i.val < 348 then
127
else
551))
else
(if i.val < 351 then
(if i.val < 350 then
570
else
74)
else
(if i.val < 352 then
616
else
(if i.val < 353 then
775
else
773)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
547
else
623)
else
(if i.val < 357 then
742
else
548))
else
(if i.val < 360 then
(if i.val < 359 then
121
else
753)
else
(if i.val < 361 then
680
else
572)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
602
else
776)
else
(if i.val < 365 then
639
else
567))
else
(if i.val < 368 then
(if i.val < 367 then
76
else
659)
else
(if i.val < 369 then
681
else
(if i.val < 370 then
683
else
59))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
611
else
70)
else
(if i.val < 374 then
552
else
655))
else
(if i.val < 377 then
(if i.val < 376 then
791
else
646)
else
(if i.val < 378 then
784
else
792)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
648
else
660)
else
(if i.val < 382 then
684
else
721))
else
(if i.val < 385 then
(if i.val < 384 then
588
else
537)
else
(if i.val < 386 then
651
else
(if i.val < 387 then
84
else
539)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
722
else
560)
else
(if i.val < 391 then
542
else
561))
else
(if i.val < 394 then
(if i.val < 393 then
686
else
79)
else
(if i.val < 395 then
741
else
85)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
661
else
781)
else
(if i.val < 399 then
95
else
538))
else
(if i.val < 402 then
(if i.val < 401 then
94
else
669)
else
(if i.val < 403 then
730
else
(if i.val < 404 then
60
else
715))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
618
else
663)
else
(if i.val < 408 then
586
else
557))
else
(if i.val < 411 then
(if i.val < 410 then
704
else
691)
else
(if i.val < 412 then
120
else
605)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
78
else
58)
else
(if i.val < 416 then
785
else
598))
else
(if i.val < 419 then
(if i.val < 418 then
612
else
81)
else
(if i.val < 420 then
654
else
716))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
723
else
707)
else
(if i.val < 424 then
559
else
705))
else
(if i.val < 427 then
(if i.val < 426 then
692
else
724)
else
(if i.val < 428 then
587
else
610)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
553
else
608)
else
(if i.val < 432 then
631
else
649))
else
(if i.val < 435 then
(if i.val < 434 then
103
else
772)
else
(if i.val < 436 then
597
else
(if i.val < 437 then
774
else
735))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
563
else
546)
else
(if i.val < 441 then
554
else
114))
else
(if i.val < 444 then
(if i.val < 443 then
568
else
544)
else
(if i.val < 445 then
55
else
67)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
111
else
72)
else
(if i.val < 449 then
555
else
93))
else
(if i.val < 452 then
(if i.val < 451 then
737
else
690)
else
(if i.val < 453 then
90
else
(if i.val < 454 then
733
else
739)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
647
else
751)
else
(if i.val < 458 then
757
else
97))
else
(if i.val < 461 then
(if i.val < 460 then
752
else
754)
else
(if i.val < 462 then
747
else
630)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
73
else
640)
else
(if i.val < 466 then
756
else
112))
else
(if i.val < 469 then
(if i.val < 468 then
713
else
621)
else
(if i.val < 470 then
666
else
(if i.val < 471 then
549
else
622)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
714
else
65)
else
(if i.val < 475 then
575
else
628))
else
(if i.val < 478 then
(if i.val < 477 then
626
else
765)
else
(if i.val < 479 then
574
else
677)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
672
else
664)
else
(if i.val < 483 then
636
else
769))
else
(if i.val < 486 then
(if i.val < 485 then
771
else
88)
else
(if i.val < 487 then
726
else
(if i.val < 488 then
104
else
778)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
779
else
736)
else
(if i.val < 492 then
750
else
629))
else
(if i.val < 495 then
(if i.val < 494 then
543
else
793)
else
(if i.val < 496 then
744
else
670)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
593
else
643)
else
(if i.val < 500 then
632
else
709))
else
(if i.val < 503 then
(if i.val < 502 then
763
else
117)
else
(if i.val < 504 then
698
else
(if i.val < 505 then
687
else
599))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
653
else
794)
else
(if i.val < 509 then
748
else
550))
else
(if i.val < 512 then
(if i.val < 511 then
740
else
728)
else
(if i.val < 513 then
761
else
685)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
128
else
702)
else
(if i.val < 517 then
658
else
746))
else
(if i.val < 520 then
(if i.val < 519 then
637
else
80)
else
(if i.val < 521 then
609
else
(if i.val < 522 then
615
else
118)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
545
else
712)
else
(if i.val < 526 then
727
else
562))
else
(if i.val < 529 then
(if i.val < 528 then
595
else
641)
else
(if i.val < 530 then
688
else
693)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
645
else
627)
else
(if i.val < 534 then
592
else
607))
else
(if i.val < 537 then
(if i.val < 536 then
61
else
68)
else
(if i.val < 538 then
894
else
(if i.val < 539 then
916
else
899))))))))))
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
834
else
858)
else
(if i.val < 543 then
848
else
807))
else
(if i.val < 546 then
(if i.val < 545 then
955
else
928)
else
(if i.val < 547 then
811
else
884)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
265
else
212)
else
(if i.val < 551 then
898
else
246))
else
(if i.val < 554 then
(if i.val < 553 then
958
else
214)
else
(if i.val < 555 then
242
else
272))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
924
else
847)
else
(if i.val < 559 then
209
else
936))
else
(if i.val < 562 then
(if i.val < 561 then
964
else
230)
else
(if i.val < 563 then
157
else
902)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
206
else
824)
else
(if i.val < 567 then
840
else
191))
else
(if i.val < 570 then
(if i.val < 569 then
865
else
239)
else
(if i.val < 571 then
247
else
(if i.val < 572 then
845
else
980))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
940
else
922)
else
(if i.val < 576 then
829
else
815))
else
(if i.val < 579 then
(if i.val < 578 then
982
else
892)
else
(if i.val < 580 then
266
else
905)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
839
else
810)
else
(if i.val < 584 then
813
else
976))
else
(if i.val < 587 then
(if i.val < 586 then
890
else
959)
else
(if i.val < 588 then
893
else
(if i.val < 589 then
240
else
809)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
833
else
836)
else
(if i.val < 593 then
200
else
972))
else
(if i.val < 596 then
(if i.val < 595 then
954
else
158)
else
(if i.val < 597 then
945
else
224)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
830
else
852)
else
(if i.val < 601 then
838
else
938))
else
(if i.val < 604 then
(if i.val < 603 then
808
else
866)
else
(if i.val < 605 then
885
else
(if i.val < 606 then
181
else
149)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
273
else
814)
else
(if i.val < 610 then
259
else
891))
else
(if i.val < 613 then
(if i.val < 612 then
877
else
912)
else
(if i.val < 614 then
983
else
882)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
264
else
957)
else
(if i.val < 618 then
960
else
875))
else
(if i.val < 621 then
(if i.val < 620 then
269
else
901)
else
(if i.val < 622 then
225
else
(if i.val < 623 then
229
else
165)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
841
else
895)
else
(if i.val < 627 then
258
else
194))
else
(if i.val < 630 then
(if i.val < 629 then
823
else
244)
else
(if i.val < 631 then
141
else
140)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
820
else
879)
else
(if i.val < 635 then
806
else
856))
else
(if i.val < 638 then
(if i.val < 637 then
147
else
797)
else
(if i.val < 639 then
897
else
(if i.val < 640 then
857
else
837))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
169
else
222)
else
(if i.val < 644 then
930
else
825))
else
(if i.val < 647 then
(if i.val < 646 then
184
else
276)
else
(if i.val < 648 then
821
else
933)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
973
else
854)
else
(if i.val < 652 then
932
else
889))
else
(if i.val < 655 then
(if i.val < 654 then
981
else
172)
else
(if i.val < 656 then
835
else
(if i.val < 657 then
796
else
864)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
881
else
186)
else
(if i.val < 661 then
927
else
178))
else
(if i.val < 664 then
(if i.val < 663 then
816
else
950)
else
(if i.val < 665 then
241
else
855)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
146
else
931)
else
(if i.val < 669 then
860
else
962))
else
(if i.val < 672 then
(if i.val < 671 then
799
else
925)
else
(if i.val < 673 then
846
else
(if i.val < 674 then
965
else
183))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
942
else
947)
else
(if i.val < 678 then
822
else
915))
else
(if i.val < 681 then
(if i.val < 680 then
896
else
243)
else
(if i.val < 682 then
179
else
949)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
182
else
966)
else
(if i.val < 686 then
187
else
946))
else
(if i.val < 689 then
(if i.val < 688 then
268
else
176)
else
(if i.val < 690 then
868
else
831))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
913
else
906)
else
(if i.val < 694 then
177
else
843))
else
(if i.val < 697 then
(if i.val < 696 then
873
else
904)
else
(if i.val < 698 then
900
else
956)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
827
else
844)
else
(if i.val < 702 then
801
else
185))
else
(if i.val < 705 then
(if i.val < 704 then
804
else
961)
else
(if i.val < 706 then
917
else
(if i.val < 707 then
878
else
929))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
876
else
193)
else
(if i.val < 711 then
805
else
151))
else
(if i.val < 714 then
(if i.val < 713 then
152
else
168)
else
(if i.val < 715 then
231
else
850)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
207
else
199)
else
(if i.val < 719 then
189
else
210))
else
(if i.val < 722 then
(if i.val < 721 then
196
else
874)
else
(if i.val < 723 then
934
else
(if i.val < 724 then
944
else
951)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
197
else
260)
else
(if i.val < 728 then
154
else
828))
else
(if i.val < 731 then
(if i.val < 730 then
977
else
918)
else
(if i.val < 732 then
867
else
920)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
812
else
908)
else
(if i.val < 736 then
215
else
218))
else
(if i.val < 739 then
(if i.val < 738 then
223
else
886)
else
(if i.val < 740 then
228
else
(if i.val < 741 then
832
else
281)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
911
else
217)
else
(if i.val < 745 then
971
else
910))
else
(if i.val < 748 then
(if i.val < 747 then
277
else
968)
else
(if i.val < 749 then
862
else
903)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
145
else
161)
else
(if i.val < 753 then
163
else
227))
else
(if i.val < 756 then
(if i.val < 755 then
270
else
914)
else
(if i.val < 757 then
817
else
(if i.val < 758 then
948
else
963)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
941
else
937)
else
(if i.val < 762 then
201
else
887))
else
(if i.val < 765 then
(if i.val < 764 then
853
else
935)
else
(if i.val < 766 then
190
else
803)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
851
else
975)
else
(if i.val < 770 then
923
else
907))
else
(if i.val < 773 then
(if i.val < 772 then
219
else
974)
else
(if i.val < 774 then
826
else
(if i.val < 775 then
798
else
263))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
282
else
271)
else
(if i.val < 779 then
170
else
138))
else
(if i.val < 782 then
(if i.val < 781 then
979
else
919)
else
(if i.val < 783 then
921
else
859)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
952
else
871)
else
(if i.val < 787 then
883
else
970))
else
(if i.val < 790 then
(if i.val < 789 then
863
else
818)
else
(if i.val < 791 then
953
else
(if i.val < 792 then
888
else
909)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
800
else
872)
else
(if i.val < 796 then
1008
else
1031))
else
(if i.val < 799 then
(if i.val < 798 then
518
else
436)
else
(if i.val < 800 then
496
else
494)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
1032
else
1012)
else
(if i.val < 804 then
1047
else
306))
else
(if i.val < 807 then
(if i.val < 806 then
299
else
994)
else
(if i.val < 808 then
493
else
(if i.val < 809 then
362
else
991)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
317
else
439)
else
(if i.val < 813 then
453
else
1005))
else
(if i.val < 816 then
(if i.val < 815 then
430
else
330)
else
(if i.val < 817 then
997
else
465)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
1007
else
1025)
else
(if i.val < 821 then
499
else
455))
else
(if i.val < 824 then
(if i.val < 823 then
479
else
475)
else
(if i.val < 825 then
1033
else
1063))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
353
else
1037)
else
(if i.val < 829 then
511
else
474))
else
(if i.val < 832 then
(if i.val < 831 then
416
else
451)
else
(if i.val < 833 then
510
else
1017)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
1061
else
374)
else
(if i.val < 837 then
992
else
464))
else
(if i.val < 840 then
(if i.val < 839 then
1046
else
1034)
else
(if i.val < 841 then
312
else
(if i.val < 842 then
1059
else
1048))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
1053
else
310)
else
(if i.val < 846 then
1022
else
480))
else
(if i.val < 849 then
(if i.val < 848 then
408
else
390)
else
(if i.val < 850 then
1058
else
404)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
1006
else
505)
else
(if i.val < 854 then
501
else
1039))
else
(if i.val < 857 then
(if i.val < 856 then
1045
else
1000)
else
(if i.val < 858 then
364
else
(if i.val < 859 then
1021
else
998)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
1057
else
985)
else
(if i.val < 863 then
508
else
324))
else
(if i.val < 866 then
(if i.val < 865 then
1011
else
442)
else
(if i.val < 867 then
1041
else
1015)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
1020
else
1049)
else
(if i.val < 871 then
1060
else
415))
else
(if i.val < 874 then
(if i.val < 873 then
507
else
1002)
else
(if i.val < 875 then
382
else
(if i.val < 876 then
405
else
1010)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
371
else
1019)
else
(if i.val < 880 then
1038
else
1016))
else
(if i.val < 883 then
(if i.val < 882 then
516
else
995)
else
(if i.val < 884 then
987
else
354)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
332
else
341)
else
(if i.val < 888 then
320
else
375))
else
(if i.val < 891 then
(if i.val < 890 then
1026
else
993)
else
(if i.val < 892 then
428
else
(if i.val < 893 then
305
else
427)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
384
else
1003)
else
(if i.val < 897 then
986
else
1064))
else
(if i.val < 900 then
(if i.val < 899 then
509
else
387)
else
(if i.val < 901 then
996
else
333)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
438
else
1050)
else
(if i.val < 905 then
1035
else
1018))
else
(if i.val < 908 then
(if i.val < 907 then
425
else
318)
else
(if i.val < 909 then
989
else
(if i.val < 910 then
378
else
1030))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
356
else
417)
else
(if i.val < 914 then
410
else
319))
else
(if i.val < 917 then
(if i.val < 916 then
1040
else
399)
else
(if i.val < 918 then
424
else
402)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
397
else
327)
else
(if i.val < 922 then
1062
else
478))
else
(if i.val < 925 then
(if i.val < 924 then
483
else
316)
else
(if i.val < 926 then
1014
else
(if i.val < 927 then
1013
else
380)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
523
else
422)
else
(if i.val < 931 then
498
else
1054))
else
(if i.val < 934 then
(if i.val < 933 then
385
else
379)
else
(if i.val < 935 then
388
else
1042)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
423
else
311)
else
(if i.val < 939 then
1051
else
1043))
else
(if i.val < 942 then
(if i.val < 941 then
990
else
295)
else
(if i.val < 943 then
984
else
(if i.val < 944 then
1023
else
421))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
1028
else
392)
else
(if i.val < 948 then
1009
else
457))
else
(if i.val < 951 then
(if i.val < 950 then
1036
else
406)
else
(if i.val < 952 then
426
else
377)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
313
else
1052)
else
(if i.val < 956 then
443
else
503))
else
(if i.val < 959 then
(if i.val < 958 then
351
else
373)
else
(if i.val < 960 then
407
else
1001))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
409
else
401)
else
(if i.val < 964 then
297
else
389))
else
(if i.val < 967 then
(if i.val < 966 then
325
else
381)
else
(if i.val < 968 then
1027
else
461)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
1024
else
335)
else
(if i.val < 972 then
495
else
497))
else
(if i.val < 975 then
(if i.val < 974 then
432
else
434)
else
(if i.val < 976 then
1004
else
(if i.val < 977 then
1055
else
1056))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
1029
else
999)
else
(if i.val < 981 then
361
else
506))
else
(if i.val < 984 then
(if i.val < 983 then
1044
else
988)
else
(if i.val < 985 then
675
else
1075)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
679
else
786)
else
(if i.val < 989 then
613
else
734))
else
(if i.val < 992 then
(if i.val < 991 then
573
else
589)
else
(if i.val < 993 then
591
else
(if i.val < 994 then
585
else
634)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
614
else
697)
else
(if i.val < 998 then
662
else
783))
else
(if i.val < 1001 then
(if i.val < 1000 then
780
else
635)
else
(if i.val < 1002 then
617
else
695)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
625
else
768)
else
(if i.val < 1006 then
583
else
767))
else
(if i.val < 1009 then
(if i.val < 1008 then
789
else
1076)
else
(if i.val < 1010 then
676
else
(if i.val < 1011 then
708
else
657)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
1074
else
1078)
else
(if i.val < 1015 then
671
else
731))
else
(if i.val < 1018 then
(if i.val < 1017 then
1066
else
590)
else
(if i.val < 1019 then
580
else
706)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
689
else
541)
else
(if i.val < 1023 then
571
else
1073))
else
(if i.val < 1026 then
(if i.val < 1025 then
1071
else
1079)
else
(if i.val < 1027 then
652
else
(if i.val < 1028 then
1072
else
596)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
1069
else
745)
else
(if i.val < 1032 then
656
else
701))
else
(if i.val < 1035 then
(if i.val < 1034 then
565
else
581)
else
(if i.val < 1036 then
696
else
682)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
699
else
633)
else
(if i.val < 1040 then
650
else
678))
else
(if i.val < 1043 then
(if i.val < 1042 then
603
else
764)
else
(if i.val < 1044 then
1068
else
(if i.val < 1045 then
577
else
665))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
600
else
766)
else
(if i.val < 1049 then
1070
else
1077))
else
(if i.val < 1052 then
(if i.val < 1051 then
749
else
601)
else
(if i.val < 1053 then
594
else
694)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
667
else
584)
else
(if i.val < 1057 then
729
else
668))
else
(if i.val < 1060 then
(if i.val < 1059 then
1065
else
624)
else
(if i.val < 1061 then
1067
else
(if i.val < 1062 then
540
else
782)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
644
else
638)
else
(if i.val < 1066 then
849
else
880))
else
(if i.val < 1069 then
(if i.val < 1068 then
870
else
939)
else
(if i.val < 1070 then
978
else
842)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
969
else
967)
else
(if i.val < 1074 then
943
else
802))
else
(if i.val < 1077 then
(if i.val < 1076 then
861
else
795)
else
(if i.val < 1078 then
869
else
(if i.val < 1079 then
926
else
819)))))))))))

def g32p_row06_cosetGeneratorNext : Fin 4 → Fin 1080 → Fin 1080 :=
  ![g32p_row06_cosetGeneratorNextColumn0, g32p_row06_cosetGeneratorNextColumn1, g32p_row06_cosetGeneratorNextColumn2, g32p_row06_cosetGeneratorNextColumn3]

def g32p_row06_cosetGeneratorFactorColumn0 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 540 then
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
(if i.val < 32 then
0
else
0))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
0
else
0)
else
(if i.val < 36 then
0
else
0))
else
(if i.val < 39 then
(if i.val < 38 then
0
else
0)
else
(if i.val < 40 then
0
else
0)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
0
else
0)
else
(if i.val < 44 then
0
else
0))
else
(if i.val < 47 then
(if i.val < 46 then
0
else
0)
else
(if i.val < 48 then
0
else
(if i.val < 49 then
0
else
0)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
0
else
0)
else
(if i.val < 53 then
0
else
0))
else
(if i.val < 56 then
(if i.val < 55 then
0
else
0)
else
(if i.val < 57 then
0
else
0)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
0
else
0)
else
(if i.val < 61 then
0
else
0))
else
(if i.val < 64 then
(if i.val < 63 then
0
else
0)
else
(if i.val < 65 then
0
else
(if i.val < 66 then
0
else
0)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
0
else
0)
else
(if i.val < 70 then
0
else
0))
else
(if i.val < 73 then
(if i.val < 72 then
0
else
0)
else
(if i.val < 74 then
0
else
0)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
0
else
0)
else
(if i.val < 78 then
0
else
0))
else
(if i.val < 81 then
(if i.val < 80 then
0
else
0)
else
(if i.val < 82 then
0
else
(if i.val < 83 then
0
else
0)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
0
else
0))
else
(if i.val < 90 then
(if i.val < 89 then
0
else
0)
else
(if i.val < 91 then
0
else
0)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
0
else
0)
else
(if i.val < 95 then
0
else
0))
else
(if i.val < 98 then
(if i.val < 97 then
0
else
0)
else
(if i.val < 99 then
0
else
(if i.val < 100 then
0
else
0))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
0
else
0)
else
(if i.val < 104 then
0
else
0))
else
(if i.val < 107 then
(if i.val < 106 then
0
else
0)
else
(if i.val < 108 then
0
else
0)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
0
else
0)
else
(if i.val < 112 then
0
else
0))
else
(if i.val < 115 then
(if i.val < 114 then
0
else
0)
else
(if i.val < 116 then
0
else
(if i.val < 117 then
0
else
0)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
0
else
0)
else
(if i.val < 121 then
0
else
0))
else
(if i.val < 124 then
(if i.val < 123 then
0
else
0)
else
(if i.val < 125 then
0
else
0)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
0
else
0)
else
(if i.val < 129 then
0
else
0))
else
(if i.val < 132 then
(if i.val < 131 then
0
else
0)
else
(if i.val < 133 then
0
else
(if i.val < 134 then
0
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
0
else
0)
else
(if i.val < 138 then
0
else
0))
else
(if i.val < 141 then
(if i.val < 140 then
0
else
0)
else
(if i.val < 142 then
0
else
0)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
0
else
0)
else
(if i.val < 146 then
0
else
0))
else
(if i.val < 149 then
(if i.val < 148 then
0
else
0)
else
(if i.val < 150 then
0
else
0))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
0
else
0)
else
(if i.val < 154 then
0
else
0))
else
(if i.val < 157 then
(if i.val < 156 then
0
else
0)
else
(if i.val < 158 then
0
else
0)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
0
else
0)
else
(if i.val < 162 then
0
else
0))
else
(if i.val < 165 then
(if i.val < 164 then
0
else
0)
else
(if i.val < 166 then
0
else
(if i.val < 167 then
0
else
0))))))
else
(if i.val < 185 then
(if i.val < 176 then
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
0)))
else
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
(if i.val < 184 then
0
else
0)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
0
else
0)
else
(if i.val < 188 then
0
else
0))
else
(if i.val < 191 then
(if i.val < 190 then
0
else
0)
else
(if i.val < 192 then
0
else
0)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
0
else
0)
else
(if i.val < 196 then
0
else
0))
else
(if i.val < 199 then
(if i.val < 198 then
0
else
0)
else
(if i.val < 200 then
0
else
(if i.val < 201 then
0
else
0)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
0
else
0)
else
(if i.val < 205 then
0
else
0))
else
(if i.val < 208 then
(if i.val < 207 then
0
else
0)
else
(if i.val < 209 then
0
else
0)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
0
else
0)
else
(if i.val < 213 then
0
else
0))
else
(if i.val < 216 then
(if i.val < 215 then
0
else
0)
else
(if i.val < 217 then
0
else
(if i.val < 218 then
0
else
0)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
0
else
0)
else
(if i.val < 222 then
0
else
0))
else
(if i.val < 225 then
(if i.val < 224 then
0
else
0)
else
(if i.val < 226 then
0
else
0)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
0
else
0)
else
(if i.val < 230 then
0
else
0))
else
(if i.val < 233 then
(if i.val < 232 then
0
else
0)
else
(if i.val < 234 then
0
else
(if i.val < 235 then
0
else
0))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
0))
else
(if i.val < 242 then
(if i.val < 241 then
0
else
0)
else
(if i.val < 243 then
0
else
0)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
0
else
0)
else
(if i.val < 247 then
0
else
0))
else
(if i.val < 250 then
(if i.val < 249 then
0
else
0)
else
(if i.val < 251 then
0
else
(if i.val < 252 then
0
else
0)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
0
else
0)
else
(if i.val < 256 then
0
else
0))
else
(if i.val < 259 then
(if i.val < 258 then
0
else
0)
else
(if i.val < 260 then
0
else
0)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
0
else
0)
else
(if i.val < 264 then
0
else
0))
else
(if i.val < 267 then
(if i.val < 266 then
0
else
0)
else
(if i.val < 268 then
0
else
(if i.val < 269 then
0
else
0)))))))))
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
0)
else
(if i.val < 273 then
0
else
0))
else
(if i.val < 276 then
(if i.val < 275 then
0
else
0)
else
(if i.val < 277 then
0
else
0)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
0
else
0)
else
(if i.val < 281 then
0
else
0))
else
(if i.val < 284 then
(if i.val < 283 then
0
else
0)
else
(if i.val < 285 then
0
else
0))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
0
else
0)
else
(if i.val < 289 then
0
else
0))
else
(if i.val < 292 then
(if i.val < 291 then
0
else
0)
else
(if i.val < 293 then
0
else
0)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
0
else
0)
else
(if i.val < 297 then
0
else
0))
else
(if i.val < 300 then
(if i.val < 299 then
0
else
0)
else
(if i.val < 301 then
0
else
(if i.val < 302 then
0
else
0))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
0
else
0)
else
(if i.val < 306 then
0
else
0))
else
(if i.val < 309 then
(if i.val < 308 then
0
else
0)
else
(if i.val < 310 then
0
else
0)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
0
else
0)
else
(if i.val < 314 then
0
else
0))
else
(if i.val < 317 then
(if i.val < 316 then
0
else
0)
else
(if i.val < 318 then
0
else
(if i.val < 319 then
0
else
0)))))
else
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
(if i.val < 336 then
0
else
0)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
0
else
0)
else
(if i.val < 340 then
0
else
0))
else
(if i.val < 343 then
(if i.val < 342 then
0
else
0)
else
(if i.val < 344 then
0
else
0)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
0
else
0)
else
(if i.val < 348 then
0
else
0))
else
(if i.val < 351 then
(if i.val < 350 then
0
else
0)
else
(if i.val < 352 then
0
else
(if i.val < 353 then
0
else
0)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
0
else
0)
else
(if i.val < 357 then
0
else
0))
else
(if i.val < 360 then
(if i.val < 359 then
0
else
0)
else
(if i.val < 361 then
0
else
0)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
0
else
0)
else
(if i.val < 365 then
0
else
0))
else
(if i.val < 368 then
(if i.val < 367 then
0
else
0)
else
(if i.val < 369 then
0
else
(if i.val < 370 then
0
else
0))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
0
else
0)
else
(if i.val < 374 then
0
else
0))
else
(if i.val < 377 then
(if i.val < 376 then
0
else
0)
else
(if i.val < 378 then
0
else
0)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
0
else
0)
else
(if i.val < 382 then
0
else
0))
else
(if i.val < 385 then
(if i.val < 384 then
0
else
0)
else
(if i.val < 386 then
0
else
(if i.val < 387 then
0
else
0)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
0
else
0)
else
(if i.val < 391 then
0
else
0))
else
(if i.val < 394 then
(if i.val < 393 then
0
else
0)
else
(if i.val < 395 then
0
else
0)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
0
else
0)
else
(if i.val < 399 then
0
else
0))
else
(if i.val < 402 then
(if i.val < 401 then
0
else
0)
else
(if i.val < 403 then
0
else
(if i.val < 404 then
0
else
0))))))))
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
0)
else
(if i.val < 408 then
0
else
0))
else
(if i.val < 411 then
(if i.val < 410 then
0
else
0)
else
(if i.val < 412 then
0
else
0)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
0
else
0)
else
(if i.val < 416 then
0
else
0))
else
(if i.val < 419 then
(if i.val < 418 then
0
else
0)
else
(if i.val < 420 then
0
else
0))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
0
else
0)
else
(if i.val < 424 then
0
else
0))
else
(if i.val < 427 then
(if i.val < 426 then
0
else
0)
else
(if i.val < 428 then
0
else
0)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
0
else
0)
else
(if i.val < 432 then
0
else
0))
else
(if i.val < 435 then
(if i.val < 434 then
0
else
0)
else
(if i.val < 436 then
0
else
(if i.val < 437 then
0
else
0))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
0
else
0)
else
(if i.val < 441 then
0
else
0))
else
(if i.val < 444 then
(if i.val < 443 then
0
else
0)
else
(if i.val < 445 then
0
else
0)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
0
else
0)
else
(if i.val < 449 then
0
else
0))
else
(if i.val < 452 then
(if i.val < 451 then
0
else
0)
else
(if i.val < 453 then
0
else
(if i.val < 454 then
0
else
0)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
0
else
0)
else
(if i.val < 458 then
0
else
0))
else
(if i.val < 461 then
(if i.val < 460 then
0
else
0)
else
(if i.val < 462 then
0
else
0)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
0
else
0)
else
(if i.val < 466 then
0
else
0))
else
(if i.val < 469 then
(if i.val < 468 then
0
else
0)
else
(if i.val < 470 then
0
else
(if i.val < 471 then
0
else
0)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
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
0)))
else
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
(if i.val < 488 then
0
else
0)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
0
else
0)
else
(if i.val < 492 then
0
else
0))
else
(if i.val < 495 then
(if i.val < 494 then
0
else
0)
else
(if i.val < 496 then
0
else
0)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
0
else
0)
else
(if i.val < 500 then
0
else
0))
else
(if i.val < 503 then
(if i.val < 502 then
0
else
0)
else
(if i.val < 504 then
0
else
(if i.val < 505 then
0
else
0))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
0
else
0)
else
(if i.val < 509 then
0
else
0))
else
(if i.val < 512 then
(if i.val < 511 then
0
else
0)
else
(if i.val < 513 then
0
else
0)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
0
else
0)
else
(if i.val < 517 then
0
else
0))
else
(if i.val < 520 then
(if i.val < 519 then
0
else
0)
else
(if i.val < 521 then
0
else
(if i.val < 522 then
0
else
0)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
0
else
0)
else
(if i.val < 526 then
0
else
0))
else
(if i.val < 529 then
(if i.val < 528 then
0
else
0)
else
(if i.val < 530 then
0
else
0)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
0
else
0)
else
(if i.val < 534 then
0
else
0))
else
(if i.val < 537 then
(if i.val < 536 then
0
else
0)
else
(if i.val < 538 then
0
else
(if i.val < 539 then
0
else
0))))))))))
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
0)
else
(if i.val < 543 then
0
else
0))
else
(if i.val < 546 then
(if i.val < 545 then
0
else
0)
else
(if i.val < 547 then
0
else
0)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
0
else
0)
else
(if i.val < 551 then
0
else
0))
else
(if i.val < 554 then
(if i.val < 553 then
0
else
0)
else
(if i.val < 555 then
0
else
0))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
0
else
0)
else
(if i.val < 559 then
0
else
0))
else
(if i.val < 562 then
(if i.val < 561 then
0
else
0)
else
(if i.val < 563 then
0
else
0)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
0
else
0)
else
(if i.val < 567 then
0
else
0))
else
(if i.val < 570 then
(if i.val < 569 then
0
else
0)
else
(if i.val < 571 then
0
else
(if i.val < 572 then
0
else
0))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
0
else
0)
else
(if i.val < 576 then
0
else
0))
else
(if i.val < 579 then
(if i.val < 578 then
0
else
0)
else
(if i.val < 580 then
0
else
0)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
0
else
0)
else
(if i.val < 584 then
0
else
0))
else
(if i.val < 587 then
(if i.val < 586 then
0
else
0)
else
(if i.val < 588 then
0
else
(if i.val < 589 then
0
else
0)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
0
else
0)
else
(if i.val < 593 then
0
else
0))
else
(if i.val < 596 then
(if i.val < 595 then
0
else
0)
else
(if i.val < 597 then
0
else
0)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
0
else
0)
else
(if i.val < 601 then
0
else
0))
else
(if i.val < 604 then
(if i.val < 603 then
0
else
0)
else
(if i.val < 605 then
0
else
(if i.val < 606 then
0
else
0)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
0
else
0)
else
(if i.val < 610 then
0
else
0))
else
(if i.val < 613 then
(if i.val < 612 then
0
else
0)
else
(if i.val < 614 then
0
else
0)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
0
else
0)
else
(if i.val < 618 then
0
else
0))
else
(if i.val < 621 then
(if i.val < 620 then
0
else
0)
else
(if i.val < 622 then
0
else
(if i.val < 623 then
0
else
0)))))
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
(if i.val < 640 then
0
else
0))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
0
else
0)
else
(if i.val < 644 then
0
else
0))
else
(if i.val < 647 then
(if i.val < 646 then
0
else
0)
else
(if i.val < 648 then
0
else
0)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
0
else
0)
else
(if i.val < 652 then
0
else
0))
else
(if i.val < 655 then
(if i.val < 654 then
0
else
0)
else
(if i.val < 656 then
0
else
(if i.val < 657 then
0
else
0)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
0
else
0)
else
(if i.val < 661 then
0
else
0))
else
(if i.val < 664 then
(if i.val < 663 then
0
else
0)
else
(if i.val < 665 then
0
else
0)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
0
else
0)
else
(if i.val < 669 then
0
else
0))
else
(if i.val < 672 then
(if i.val < 671 then
0
else
0)
else
(if i.val < 673 then
0
else
(if i.val < 674 then
0
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
0
else
0)
else
(if i.val < 678 then
0
else
0))
else
(if i.val < 681 then
(if i.val < 680 then
0
else
0)
else
(if i.val < 682 then
0
else
0)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
0
else
0)
else
(if i.val < 686 then
0
else
0))
else
(if i.val < 689 then
(if i.val < 688 then
0
else
0)
else
(if i.val < 690 then
0
else
0))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
0
else
0)
else
(if i.val < 694 then
0
else
0))
else
(if i.val < 697 then
(if i.val < 696 then
0
else
0)
else
(if i.val < 698 then
0
else
0)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
0
else
0)
else
(if i.val < 702 then
0
else
0))
else
(if i.val < 705 then
(if i.val < 704 then
0
else
0)
else
(if i.val < 706 then
0
else
(if i.val < 707 then
0
else
0))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
0
else
0)
else
(if i.val < 711 then
0
else
0))
else
(if i.val < 714 then
(if i.val < 713 then
0
else
0)
else
(if i.val < 715 then
0
else
0)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
0
else
0)
else
(if i.val < 719 then
0
else
0))
else
(if i.val < 722 then
(if i.val < 721 then
0
else
0)
else
(if i.val < 723 then
0
else
(if i.val < 724 then
0
else
0)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
0
else
0)
else
(if i.val < 728 then
0
else
0))
else
(if i.val < 731 then
(if i.val < 730 then
0
else
0)
else
(if i.val < 732 then
0
else
0)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
0
else
0)
else
(if i.val < 736 then
0
else
0))
else
(if i.val < 739 then
(if i.val < 738 then
0
else
0)
else
(if i.val < 740 then
0
else
(if i.val < 741 then
0
else
0)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
0
else
0)
else
(if i.val < 745 then
0
else
0))
else
(if i.val < 748 then
(if i.val < 747 then
0
else
0)
else
(if i.val < 749 then
0
else
0)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
0
else
0)
else
(if i.val < 753 then
0
else
0))
else
(if i.val < 756 then
(if i.val < 755 then
0
else
0)
else
(if i.val < 757 then
0
else
(if i.val < 758 then
0
else
0)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
0
else
0)
else
(if i.val < 762 then
0
else
0))
else
(if i.val < 765 then
(if i.val < 764 then
0
else
0)
else
(if i.val < 766 then
0
else
0)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
0
else
0)
else
(if i.val < 770 then
0
else
0))
else
(if i.val < 773 then
(if i.val < 772 then
0
else
0)
else
(if i.val < 774 then
0
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
0)))
else
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
(if i.val < 792 then
0
else
0)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
0
else
0)
else
(if i.val < 796 then
0
else
0))
else
(if i.val < 799 then
(if i.val < 798 then
0
else
0)
else
(if i.val < 800 then
0
else
0)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
0
else
0)
else
(if i.val < 804 then
0
else
0))
else
(if i.val < 807 then
(if i.val < 806 then
0
else
0)
else
(if i.val < 808 then
0
else
(if i.val < 809 then
0
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
0
else
0)
else
(if i.val < 813 then
0
else
0))
else
(if i.val < 816 then
(if i.val < 815 then
0
else
0)
else
(if i.val < 817 then
0
else
0)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
0
else
0)
else
(if i.val < 821 then
0
else
0))
else
(if i.val < 824 then
(if i.val < 823 then
0
else
0)
else
(if i.val < 825 then
0
else
0))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
0
else
0)
else
(if i.val < 829 then
0
else
0))
else
(if i.val < 832 then
(if i.val < 831 then
0
else
0)
else
(if i.val < 833 then
0
else
0)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
0
else
0)
else
(if i.val < 837 then
0
else
0))
else
(if i.val < 840 then
(if i.val < 839 then
0
else
0)
else
(if i.val < 841 then
0
else
(if i.val < 842 then
0
else
0))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
0
else
0)
else
(if i.val < 846 then
0
else
0))
else
(if i.val < 849 then
(if i.val < 848 then
0
else
0)
else
(if i.val < 850 then
0
else
0)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
0
else
0)
else
(if i.val < 854 then
0
else
0))
else
(if i.val < 857 then
(if i.val < 856 then
0
else
0)
else
(if i.val < 858 then
0
else
(if i.val < 859 then
0
else
0)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
0
else
0)
else
(if i.val < 863 then
0
else
0))
else
(if i.val < 866 then
(if i.val < 865 then
0
else
0)
else
(if i.val < 867 then
0
else
0)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
0
else
0)
else
(if i.val < 871 then
0
else
0))
else
(if i.val < 874 then
(if i.val < 873 then
0
else
0)
else
(if i.val < 875 then
0
else
(if i.val < 876 then
0
else
0)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
0
else
0)
else
(if i.val < 880 then
0
else
0))
else
(if i.val < 883 then
(if i.val < 882 then
0
else
0)
else
(if i.val < 884 then
0
else
0)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
0
else
0)
else
(if i.val < 888 then
0
else
0))
else
(if i.val < 891 then
(if i.val < 890 then
0
else
0)
else
(if i.val < 892 then
0
else
(if i.val < 893 then
0
else
0)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
0
else
0)
else
(if i.val < 897 then
0
else
0))
else
(if i.val < 900 then
(if i.val < 899 then
0
else
0)
else
(if i.val < 901 then
0
else
0)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
0
else
0)
else
(if i.val < 905 then
0
else
0))
else
(if i.val < 908 then
(if i.val < 907 then
0
else
0)
else
(if i.val < 909 then
0
else
(if i.val < 910 then
0
else
0))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
0
else
0)
else
(if i.val < 914 then
0
else
0))
else
(if i.val < 917 then
(if i.val < 916 then
0
else
0)
else
(if i.val < 918 then
0
else
0)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
0
else
0)
else
(if i.val < 922 then
0
else
0))
else
(if i.val < 925 then
(if i.val < 924 then
0
else
0)
else
(if i.val < 926 then
0
else
(if i.val < 927 then
0
else
0)))))
else
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
(if i.val < 944 then
0
else
0))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
0
else
0)
else
(if i.val < 948 then
0
else
0))
else
(if i.val < 951 then
(if i.val < 950 then
0
else
0)
else
(if i.val < 952 then
0
else
0)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
0
else
0)
else
(if i.val < 956 then
0
else
0))
else
(if i.val < 959 then
(if i.val < 958 then
0
else
0)
else
(if i.val < 960 then
0
else
0))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
0
else
0)
else
(if i.val < 964 then
0
else
0))
else
(if i.val < 967 then
(if i.val < 966 then
0
else
0)
else
(if i.val < 968 then
0
else
0)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
0
else
0)
else
(if i.val < 972 then
0
else
0))
else
(if i.val < 975 then
(if i.val < 974 then
0
else
0)
else
(if i.val < 976 then
0
else
(if i.val < 977 then
0
else
0))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
0
else
0)
else
(if i.val < 981 then
0
else
0))
else
(if i.val < 984 then
(if i.val < 983 then
0
else
0)
else
(if i.val < 985 then
0
else
0)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
0
else
0)
else
(if i.val < 989 then
0
else
0))
else
(if i.val < 992 then
(if i.val < 991 then
0
else
0)
else
(if i.val < 993 then
0
else
(if i.val < 994 then
0
else
0)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
0
else
0)
else
(if i.val < 998 then
0
else
0))
else
(if i.val < 1001 then
(if i.val < 1000 then
0
else
0)
else
(if i.val < 1002 then
0
else
0)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
0
else
0)
else
(if i.val < 1006 then
0
else
0))
else
(if i.val < 1009 then
(if i.val < 1008 then
0
else
0)
else
(if i.val < 1010 then
0
else
(if i.val < 1011 then
0
else
0)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
0
else
0)
else
(if i.val < 1015 then
0
else
0))
else
(if i.val < 1018 then
(if i.val < 1017 then
0
else
0)
else
(if i.val < 1019 then
0
else
0)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
0
else
0)
else
(if i.val < 1023 then
0
else
0))
else
(if i.val < 1026 then
(if i.val < 1025 then
0
else
0)
else
(if i.val < 1027 then
0
else
(if i.val < 1028 then
0
else
0)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
0
else
0)
else
(if i.val < 1032 then
0
else
0))
else
(if i.val < 1035 then
(if i.val < 1034 then
0
else
0)
else
(if i.val < 1036 then
0
else
0)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
0
else
0)
else
(if i.val < 1040 then
0
else
0))
else
(if i.val < 1043 then
(if i.val < 1042 then
0
else
0)
else
(if i.val < 1044 then
0
else
(if i.val < 1045 then
0
else
0))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
0
else
0)
else
(if i.val < 1049 then
0
else
0))
else
(if i.val < 1052 then
(if i.val < 1051 then
0
else
0)
else
(if i.val < 1053 then
0
else
0)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
0
else
0)
else
(if i.val < 1057 then
0
else
0))
else
(if i.val < 1060 then
(if i.val < 1059 then
0
else
0)
else
(if i.val < 1061 then
0
else
(if i.val < 1062 then
0
else
0)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
0
else
0)
else
(if i.val < 1066 then
0
else
0))
else
(if i.val < 1069 then
(if i.val < 1068 then
0
else
0)
else
(if i.val < 1070 then
0
else
0)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
0
else
0)
else
(if i.val < 1074 then
0
else
0))
else
(if i.val < 1077 then
(if i.val < 1076 then
0
else
0)
else
(if i.val < 1078 then
0
else
(if i.val < 1079 then
0
else
0)))))))))))

def g32p_row06_cosetGeneratorFactorColumn1 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 540 then
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
88))
else
(if i.val < 30 then
(if i.val < 29 then
60
else
0)
else
(if i.val < 31 then
0
else
(if i.val < 32 then
0
else
0))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
0
else
0)
else
(if i.val < 36 then
0
else
0))
else
(if i.val < 39 then
(if i.val < 38 then
0
else
87)
else
(if i.val < 40 then
0
else
60)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
0
else
0)
else
(if i.val < 44 then
0
else
0))
else
(if i.val < 47 then
(if i.val < 46 then
0
else
0)
else
(if i.val < 48 then
27
else
(if i.val < 49 then
0
else
0)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
0
else
0)
else
(if i.val < 53 then
0
else
0))
else
(if i.val < 56 then
(if i.val < 55 then
19
else
0)
else
(if i.val < 57 then
0
else
0)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
65
else
0)
else
(if i.val < 61 then
88
else
60))
else
(if i.val < 64 then
(if i.val < 63 then
0
else
0)
else
(if i.val < 65 then
0
else
(if i.val < 66 then
0
else
0)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
0
else
0)
else
(if i.val < 70 then
0
else
0))
else
(if i.val < 73 then
(if i.val < 72 then
0
else
88)
else
(if i.val < 74 then
60
else
0)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
0
else
0)
else
(if i.val < 78 then
0
else
0))
else
(if i.val < 81 then
(if i.val < 80 then
0
else
0)
else
(if i.val < 82 then
88
else
(if i.val < 83 then
0
else
0)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
0
else
56))
else
(if i.val < 90 then
(if i.val < 89 then
0
else
0)
else
(if i.val < 91 then
65
else
87)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
0
else
0)
else
(if i.val < 95 then
0
else
0))
else
(if i.val < 98 then
(if i.val < 97 then
0
else
0)
else
(if i.val < 99 then
0
else
(if i.val < 100 then
0
else
0))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
0
else
0)
else
(if i.val < 104 then
0
else
0))
else
(if i.val < 107 then
(if i.val < 106 then
0
else
0)
else
(if i.val < 108 then
0
else
0)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
0
else
0)
else
(if i.val < 112 then
33
else
60))
else
(if i.val < 115 then
(if i.val < 114 then
0
else
88)
else
(if i.val < 116 then
0
else
(if i.val < 117 then
27
else
0)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
0
else
0)
else
(if i.val < 121 then
0
else
0))
else
(if i.val < 124 then
(if i.val < 123 then
0
else
0)
else
(if i.val < 125 then
0
else
0)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
0
else
48)
else
(if i.val < 129 then
73
else
0))
else
(if i.val < 132 then
(if i.val < 131 then
0
else
0)
else
(if i.val < 133 then
55
else
(if i.val < 134 then
0
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
0
else
0)
else
(if i.val < 138 then
0
else
0))
else
(if i.val < 141 then
(if i.val < 140 then
0
else
65)
else
(if i.val < 142 then
0
else
0)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
0
else
88)
else
(if i.val < 146 then
88
else
60))
else
(if i.val < 149 then
(if i.val < 148 then
125
else
0)
else
(if i.val < 150 then
0
else
0))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
0
else
5)
else
(if i.val < 154 then
0
else
0))
else
(if i.val < 157 then
(if i.val < 156 then
0
else
56)
else
(if i.val < 158 then
127
else
0)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
0
else
43)
else
(if i.val < 162 then
0
else
0))
else
(if i.val < 165 then
(if i.val < 164 then
0
else
0)
else
(if i.val < 166 then
0
else
(if i.val < 167 then
0
else
0))))))
else
(if i.val < 185 then
(if i.val < 176 then
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
88))
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
0)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
0)
else
(if i.val < 179 then
88
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
(if i.val < 184 then
0
else
88)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
0
else
0)
else
(if i.val < 188 then
88
else
0))
else
(if i.val < 191 then
(if i.val < 190 then
0
else
0)
else
(if i.val < 192 then
0
else
0)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
5
else
7)
else
(if i.val < 196 then
0
else
7))
else
(if i.val < 199 then
(if i.val < 198 then
0
else
0)
else
(if i.val < 200 then
0
else
(if i.val < 201 then
33
else
88)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
0
else
139)
else
(if i.val < 205 then
0
else
55))
else
(if i.val < 208 then
(if i.val < 207 then
93
else
0)
else
(if i.val < 209 then
0
else
0)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
84
else
0)
else
(if i.val < 213 then
87
else
0))
else
(if i.val < 216 then
(if i.val < 215 then
0
else
76)
else
(if i.val < 217 then
0
else
(if i.val < 218 then
5
else
5)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
0
else
0)
else
(if i.val < 222 then
0
else
127))
else
(if i.val < 225 then
(if i.val < 224 then
0
else
0)
else
(if i.val < 226 then
0
else
0)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
0
else
0)
else
(if i.val < 230 then
0
else
0))
else
(if i.val < 233 then
(if i.val < 232 then
0
else
0)
else
(if i.val < 234 then
0
else
(if i.val < 235 then
0
else
0))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
0))
else
(if i.val < 242 then
(if i.val < 241 then
0
else
0)
else
(if i.val < 243 then
0
else
72)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
7
else
0)
else
(if i.val < 247 then
7
else
87))
else
(if i.val < 250 then
(if i.val < 249 then
1
else
40)
else
(if i.val < 251 then
0
else
(if i.val < 252 then
0
else
0)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
0
else
0)
else
(if i.val < 256 then
108
else
0))
else
(if i.val < 259 then
(if i.val < 258 then
104
else
60)
else
(if i.val < 260 then
33
else
88)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
33
else
84)
else
(if i.val < 264 then
27
else
0))
else
(if i.val < 267 then
(if i.val < 266 then
0
else
0)
else
(if i.val < 268 then
48
else
(if i.val < 269 then
0
else
0)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
88
else
76)
else
(if i.val < 273 then
0
else
0))
else
(if i.val < 276 then
(if i.val < 275 then
0
else
23)
else
(if i.val < 277 then
0
else
0)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
48
else
0)
else
(if i.val < 281 then
0
else
0))
else
(if i.val < 284 then
(if i.val < 283 then
48
else
0)
else
(if i.val < 285 then
0
else
0))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
0
else
33)
else
(if i.val < 289 then
125
else
93))
else
(if i.val < 292 then
(if i.val < 291 then
0
else
76)
else
(if i.val < 293 then
0
else
27)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
62
else
0)
else
(if i.val < 297 then
0
else
65))
else
(if i.val < 300 then
(if i.val < 299 then
88
else
125)
else
(if i.val < 301 then
0
else
(if i.val < 302 then
0
else
0))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
0
else
65)
else
(if i.val < 306 then
88
else
0))
else
(if i.val < 309 then
(if i.val < 308 then
0
else
0)
else
(if i.val < 310 then
87
else
61)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
5
else
88)
else
(if i.val < 314 then
0
else
26))
else
(if i.val < 317 then
(if i.val < 316 then
127
else
127)
else
(if i.val < 318 then
0
else
(if i.val < 319 then
88
else
139)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
121
else
88)
else
(if i.val < 323 then
65
else
50))
else
(if i.val < 326 then
(if i.val < 325 then
94
else
0)
else
(if i.val < 327 then
0
else
69)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
7
else
0)
else
(if i.val < 331 then
0
else
87))
else
(if i.val < 334 then
(if i.val < 333 then
127
else
56)
else
(if i.val < 335 then
33
else
(if i.val < 336 then
27
else
26)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
125
else
56)
else
(if i.val < 340 then
55
else
93))
else
(if i.val < 343 then
(if i.val < 342 then
63
else
0)
else
(if i.val < 344 then
56
else
84)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
0
else
0)
else
(if i.val < 348 then
0
else
0))
else
(if i.val < 351 then
(if i.val < 350 then
0
else
0)
else
(if i.val < 352 then
0
else
(if i.val < 353 then
5
else
0)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
0
else
56)
else
(if i.val < 357 then
127
else
0))
else
(if i.val < 360 then
(if i.val < 359 then
0
else
0)
else
(if i.val < 361 then
0
else
0)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
0
else
0)
else
(if i.val < 365 then
0
else
0))
else
(if i.val < 368 then
(if i.val < 367 then
88
else
0)
else
(if i.val < 369 then
0
else
(if i.val < 370 then
0
else
0))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
0
else
0)
else
(if i.val < 374 then
0
else
0))
else
(if i.val < 377 then
(if i.val < 376 then
0
else
0)
else
(if i.val < 378 then
5
else
7)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
0
else
7)
else
(if i.val < 382 then
0
else
0))
else
(if i.val < 385 then
(if i.val < 384 then
0
else
0)
else
(if i.val < 386 then
139
else
(if i.val < 387 then
0
else
93)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
0
else
0)
else
(if i.val < 391 then
0
else
84))
else
(if i.val < 394 then
(if i.val < 393 then
88
else
0)
else
(if i.val < 395 then
71
else
0)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
84
else
0)
else
(if i.val < 399 then
55
else
57))
else
(if i.val < 402 then
(if i.val < 401 then
0
else
0)
else
(if i.val < 403 then
87
else
(if i.val < 404 then
5
else
10))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
7
else
93)
else
(if i.val < 408 then
0
else
5))
else
(if i.val < 411 then
(if i.val < 410 then
23
else
84)
else
(if i.val < 412 then
7
else
0)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
0
else
136)
else
(if i.val < 416 then
33
else
0))
else
(if i.val < 419 then
(if i.val < 418 then
0
else
57)
else
(if i.val < 420 then
19
else
69))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
8
else
125)
else
(if i.val < 424 then
93
else
59))
else
(if i.val < 427 then
(if i.val < 426 then
76
else
142)
else
(if i.val < 428 then
27
else
0)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
0
else
76)
else
(if i.val < 432 then
108
else
5))
else
(if i.val < 435 then
(if i.val < 434 then
27
else
1)
else
(if i.val < 436 then
0
else
(if i.val < 437 then
0
else
1))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
5
else
0)
else
(if i.val < 441 then
65
else
0))
else
(if i.val < 444 then
(if i.val < 443 then
66
else
5)
else
(if i.val < 445 then
0
else
0)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
87
else
127)
else
(if i.val < 449 then
40
else
0))
else
(if i.val < 452 then
(if i.val < 451 then
0
else
63)
else
(if i.val < 453 then
108
else
(if i.val < 454 then
94
else
0)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
0
else
0)
else
(if i.val < 458 then
0
else
0))
else
(if i.val < 461 then
(if i.val < 460 then
0
else
0)
else
(if i.val < 462 then
0
else
0)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
0
else
0)
else
(if i.val < 466 then
0
else
0))
else
(if i.val < 469 then
(if i.val < 468 then
0
else
0)
else
(if i.val < 470 then
0
else
(if i.val < 471 then
0
else
0)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
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
120))
else
(if i.val < 478 then
(if i.val < 477 then
86
else
87)
else
(if i.val < 479 then
5
else
115)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
11
else
0)
else
(if i.val < 483 then
103
else
7))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
139)
else
(if i.val < 487 then
108
else
(if i.val < 488 then
40
else
0)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
0
else
0)
else
(if i.val < 492 then
19
else
1))
else
(if i.val < 495 then
(if i.val < 494 then
33
else
106)
else
(if i.val < 496 then
0
else
33)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
0
else
0)
else
(if i.val < 500 then
48
else
1))
else
(if i.val < 503 then
(if i.val < 502 then
33
else
86)
else
(if i.val < 504 then
0
else
(if i.val < 505 then
0
else
48))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
0
else
107)
else
(if i.val < 509 then
60
else
29))
else
(if i.val < 512 then
(if i.val < 511 then
0
else
0)
else
(if i.val < 513 then
60
else
19)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
84
else
84)
else
(if i.val < 517 then
19
else
0))
else
(if i.val < 520 then
(if i.val < 519 then
0
else
0)
else
(if i.val < 521 then
33
else
(if i.val < 522 then
68
else
33)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
23
else
34)
else
(if i.val < 526 then
0
else
0))
else
(if i.val < 529 then
(if i.val < 528 then
0
else
19)
else
(if i.val < 530 then
55
else
0)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
0
else
7)
else
(if i.val < 534 then
0
else
68))
else
(if i.val < 537 then
(if i.val < 536 then
0
else
0)
else
(if i.val < 538 then
0
else
(if i.val < 539 then
88
else
125))))))))))
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
0)
else
(if i.val < 543 then
87
else
61))
else
(if i.val < 546 then
(if i.val < 545 then
5
else
27)
else
(if i.val < 547 then
0
else
26)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
127
else
127)
else
(if i.val < 551 then
0
else
0))
else
(if i.val < 554 then
(if i.val < 553 then
0
else
0)
else
(if i.val < 555 then
76
else
0))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
5
else
5)
else
(if i.val < 559 then
88
else
0))
else
(if i.val < 562 then
(if i.val < 561 then
0
else
127)
else
(if i.val < 563 then
0
else
0)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
121
else
61)
else
(if i.val < 567 then
94
else
110))
else
(if i.val < 570 then
(if i.val < 569 then
88
else
107)
else
(if i.val < 571 then
7
else
(if i.val < 572 then
0
else
7))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
117
else
127)
else
(if i.val < 576 then
56
else
26))
else
(if i.val < 579 then
(if i.val < 578 then
139
else
56)
else
(if i.val < 580 then
87
else
11)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
0
else
56)
else
(if i.val < 584 then
84
else
84))
else
(if i.val < 587 then
(if i.val < 586 then
47
else
55)
else
(if i.val < 588 then
121
else
(if i.val < 589 then
84
else
89)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
55
else
142)
else
(if i.val < 593 then
26
else
2))
else
(if i.val < 596 then
(if i.val < 595 then
87
else
5)
else
(if i.val < 597 then
9
else
125)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
0
else
19)
else
(if i.val < 601 then
127
else
23))
else
(if i.val < 604 then
(if i.val < 603 then
84
else
40)
else
(if i.val < 605 then
43
else
(if i.val < 606 then
11
else
136)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
33
else
43)
else
(if i.val < 610 then
47
else
26))
else
(if i.val < 613 then
(if i.val < 612 then
26
else
11)
else
(if i.val < 614 then
8
else
125)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
93
else
59)
else
(if i.val < 618 then
76
else
142))
else
(if i.val < 621 then
(if i.val < 620 then
27
else
0)
else
(if i.val < 622 then
0
else
(if i.val < 623 then
0
else
0)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
0
else
27)
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
139
else
121)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
65
else
50)
else
(if i.val < 635 then
94
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
87
else
(if i.val < 640 then
127
else
56))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
26
else
56)
else
(if i.val < 644 then
63
else
0))
else
(if i.val < 647 then
(if i.val < 646 then
56
else
0)
else
(if i.val < 648 then
0
else
0)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
0
else
0)
else
(if i.val < 652 then
56
else
0))
else
(if i.val < 655 then
(if i.val < 654 then
0
else
0)
else
(if i.val < 656 then
0
else
(if i.val < 657 then
0
else
0)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
0
else
0)
else
(if i.val < 661 then
0
else
139))
else
(if i.val < 664 then
(if i.val < 663 then
0
else
93)
else
(if i.val < 665 then
0
else
0)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
55
else
57)
else
(if i.val < 669 then
0
else
87))
else
(if i.val < 672 then
(if i.val < 671 then
5
else
93)
else
(if i.val < 673 then
0
else
(if i.val < 674 then
5
else
84))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
7
else
0)
else
(if i.val < 678 then
136
else
33))
else
(if i.val < 681 then
(if i.val < 680 then
0
else
57)
else
(if i.val < 682 then
19
else
69)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
59
else
142)
else
(if i.val < 686 then
71
else
0))
else
(if i.val < 689 then
(if i.val < 688 then
23
else
61)
else
(if i.val < 690 then
62
else
26))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
33
else
18)
else
(if i.val < 694 then
125
else
57))
else
(if i.val < 697 then
(if i.val < 696 then
84
else
33)
else
(if i.val < 698 then
43
else
33)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
5
else
60)
else
(if i.val < 702 then
7
else
102))
else
(if i.val < 705 then
(if i.val < 704 then
72
else
60)
else
(if i.val < 706 then
19
else
(if i.val < 707 then
84
else
84))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
19
else
7)
else
(if i.val < 711 then
48
else
0))
else
(if i.val < 714 then
(if i.val < 713 then
5
else
86)
else
(if i.val < 715 then
136
else
23)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
34
else
35)
else
(if i.val < 719 then
68
else
56))
else
(if i.val < 722 then
(if i.val < 721 then
56
else
55)
else
(if i.val < 723 then
34
else
(if i.val < 724 then
84
else
30)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
92
else
113)
else
(if i.val < 728 then
0
else
0))
else
(if i.val < 731 then
(if i.val < 730 then
0
else
1)
else
(if i.val < 732 then
25
else
88)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
66
else
7)
else
(if i.val < 736 then
108
else
7))
else
(if i.val < 739 then
(if i.val < 738 then
87
else
89)
else
(if i.val < 740 then
86
else
(if i.val < 741 then
89
else
87)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
48
else
11)
else
(if i.val < 745 then
87
else
47))
else
(if i.val < 748 then
(if i.val < 747 then
62
else
0)
else
(if i.val < 749 then
0
else
0)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
0
else
0)
else
(if i.val < 753 then
0
else
0))
else
(if i.val < 756 then
(if i.val < 755 then
0
else
0)
else
(if i.val < 757 then
0
else
(if i.val < 758 then
0
else
0)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
0
else
0)
else
(if i.val < 762 then
23
else
62))
else
(if i.val < 765 then
(if i.val < 764 then
10
else
84)
else
(if i.val < 766 then
84
else
33)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
115
else
11)
else
(if i.val < 770 then
7
else
68))
else
(if i.val < 773 then
(if i.val < 772 then
48
else
78)
else
(if i.val < 774 then
58
else
(if i.val < 775 then
30
else
34))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
129
else
58)
else
(if i.val < 779 then
9
else
54))
else
(if i.val < 782 then
(if i.val < 781 then
33
else
139)
else
(if i.val < 783 then
92
else
91)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
0
else
136)
else
(if i.val < 787 then
42
else
57))
else
(if i.val < 790 then
(if i.val < 789 then
117
else
73)
else
(if i.val < 791 then
0
else
(if i.val < 792 then
136
else
7)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
106
else
127)
else
(if i.val < 796 then
0
else
0))
else
(if i.val < 799 then
(if i.val < 798 then
87
else
61)
else
(if i.val < 800 then
27
else
88)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
0
else
127)
else
(if i.val < 804 then
0
else
60))
else
(if i.val < 807 then
(if i.val < 806 then
121
else
61)
else
(if i.val < 808 then
27
else
(if i.val < 809 then
94
else
110)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
88
else
0)
else
(if i.val < 813 then
117
else
127))
else
(if i.val < 816 then
(if i.val < 815 then
56
else
26)
else
(if i.val < 817 then
56
else
11)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
0
else
56)
else
(if i.val < 821 then
0
else
0))
else
(if i.val < 824 then
(if i.val < 823 then
108
else
27)
else
(if i.val < 825 then
0
else
26))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
0
else
1)
else
(if i.val < 829 then
0
else
65))
else
(if i.val < 832 then
(if i.val < 831 then
66
else
5)
else
(if i.val < 833 then
0
else
0)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
0
else
139)
else
(if i.val < 837 then
0
else
58))
else
(if i.val < 840 then
(if i.val < 839 then
63
else
94)
else
(if i.val < 841 then
55
else
(if i.val < 842 then
27
else
61))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
87
else
5)
else
(if i.val < 846 then
93
else
72))
else
(if i.val < 849 then
(if i.val < 848 then
25
else
126)
else
(if i.val < 850 then
7
else
138)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
141
else
33)
else
(if i.val < 854 then
47
else
57))
else
(if i.val < 857 then
(if i.val < 856 then
19
else
69)
else
(if i.val < 858 then
87
else
(if i.val < 859 then
142
else
71)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
129
else
11)
else
(if i.val < 863 then
28
else
1))
else
(if i.val < 866 then
(if i.val < 865 then
26
else
1)
else
(if i.val < 867 then
124
else
125)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
10
else
94)
else
(if i.val < 871 then
33
else
68))
else
(if i.val < 874 then
(if i.val < 873 then
73
else
137)
else
(if i.val < 875 then
107
else
(if i.val < 876 then
107
else
102)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
26
else
80)
else
(if i.val < 880 then
19
else
84))
else
(if i.val < 883 then
(if i.val < 882 then
84
else
19)
else
(if i.val < 884 then
72
else
28)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
90
else
5)
else
(if i.val < 888 then
68
else
136))
else
(if i.val < 891 then
(if i.val < 890 then
23
else
34)
else
(if i.val < 892 then
26
else
(if i.val < 893 then
106
else
56)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
43
else
57)
else
(if i.val < 897 then
141
else
0))
else
(if i.val < 900 then
(if i.val < 899 then
29
else
136)
else
(if i.val < 901 then
78
else
121)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
71
else
0)
else
(if i.val < 905 then
0
else
0))
else
(if i.val < 908 then
(if i.val < 907 then
0
else
0)
else
(if i.val < 909 then
0
else
(if i.val < 910 then
0
else
47))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
121
else
89)
else
(if i.val < 914 then
26
else
2))
else
(if i.val < 917 then
(if i.val < 916 then
19
else
43)
else
(if i.val < 918 then
11
else
43)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
47
else
0)
else
(if i.val < 922 then
0
else
0))
else
(if i.val < 925 then
(if i.val < 924 then
121
else
50)
else
(if i.val < 926 then
0
else
(if i.val < 927 then
0
else
26)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
56
else
55)
else
(if i.val < 931 then
5
else
0))
else
(if i.val < 934 then
(if i.val < 933 then
57
else
19)
else
(if i.val < 935 then
69
else
23)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
62
else
26)
else
(if i.val < 939 then
84
else
33))
else
(if i.val < 942 then
(if i.val < 941 then
33
else
102)
else
(if i.val < 943 then
72
else
(if i.val < 944 then
7
else
48))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
0
else
35)
else
(if i.val < 948 then
68
else
56))
else
(if i.val < 951 then
(if i.val < 950 then
34
else
84)
else
(if i.val < 952 then
92
else
0)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
0
else
33)
else
(if i.val < 956 then
131
else
88))
else
(if i.val < 959 then
(if i.val < 958 then
61
else
125)
else
(if i.val < 960 then
72
else
2))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
57
else
35)
else
(if i.val < 964 then
138
else
0))
else
(if i.val < 967 then
(if i.val < 966 then
136
else
142)
else
(if i.val < 968 then
8
else
127)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
66
else
108)
else
(if i.val < 972 then
65
else
62))
else
(if i.val < 975 then
(if i.val < 974 then
11
else
111)
else
(if i.val < 976 then
111
else
(if i.val < 977 then
136
else
133))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
122
else
89)
else
(if i.val < 981 then
19
else
32))
else
(if i.val < 984 then
(if i.val < 983 then
127
else
27)
else
(if i.val < 985 then
0
else
0)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
110
else
88)
else
(if i.val < 989 then
0
else
7))
else
(if i.val < 992 then
(if i.val < 991 then
0
else
33)
else
(if i.val < 993 then
33
else
(if i.val < 994 then
27
else
61)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
89
else
72)
else
(if i.val < 998 then
48
else
138))
else
(if i.val < 1001 then
(if i.val < 1000 then
48
else
47)
else
(if i.val < 1002 then
62
else
0)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
0
else
121)
else
(if i.val < 1006 then
50
else
88))
else
(if i.val < 1009 then
(if i.val < 1008 then
66
else
26)
else
(if i.val < 1010 then
68
else
(if i.val < 1011 then
55
else
127)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
11
else
11)
else
(if i.val < 1015 then
43
else
11))
else
(if i.val < 1018 then
(if i.val < 1017 then
23
else
117)
else
(if i.val < 1019 then
27
else
21)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
40
else
73)
else
(if i.val < 1023 then
102
else
72))
else
(if i.val < 1026 then
(if i.val < 1025 then
41
else
78)
else
(if i.val < 1027 then
37
else
(if i.val < 1028 then
35
else
106)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
56
else
34)
else
(if i.val < 1032 then
129
else
136))
else
(if i.val < 1035 then
(if i.val < 1034 then
111
else
95)
else
(if i.val < 1036 then
33
else
137)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
137
else
118)
else
(if i.val < 1040 then
61
else
136))
else
(if i.val < 1043 then
(if i.val < 1042 then
52
else
52)
else
(if i.val < 1044 then
21
else
(if i.val < 1045 then
138
else
127))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
136
else
63)
else
(if i.val < 1049 then
56
else
127))
else
(if i.val < 1052 then
(if i.val < 1051 then
0
else
108)
else
(if i.val < 1053 then
0
else
62)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
90
else
121)
else
(if i.val < 1057 then
71
else
125))
else
(if i.val < 1060 then
(if i.val < 1059 then
0
else
61)
else
(if i.val < 1061 then
89
else
(if i.val < 1062 then
56
else
124)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
26
else
0)
else
(if i.val < 1066 then
0
else
108))
else
(if i.val < 1069 then
(if i.val < 1068 then
93
else
62)
else
(if i.val < 1070 then
37
else
111)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
95
else
136)
else
(if i.val < 1074 then
127
else
122))
else
(if i.val < 1077 then
(if i.val < 1076 then
41
else
43)
else
(if i.val < 1078 then
124
else
(if i.val < 1079 then
127
else
8)))))))))))

def g32p_row06_cosetGeneratorFactorColumn2 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 540 then
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
57)
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
36)
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
52
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
57
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
36
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
(if i.val < 32 then
52
else
0))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
57
else
0)
else
(if i.val < 36 then
0
else
0))
else
(if i.val < 39 then
(if i.val < 38 then
0
else
0)
else
(if i.val < 40 then
87
else
0)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
0
else
0)
else
(if i.val < 44 then
0
else
0))
else
(if i.val < 47 then
(if i.val < 46 then
0
else
0)
else
(if i.val < 48 then
0
else
(if i.val < 49 then
0
else
0)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
0
else
0)
else
(if i.val < 53 then
0
else
0))
else
(if i.val < 56 then
(if i.val < 55 then
0
else
57)
else
(if i.val < 57 then
0
else
0)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
0
else
36)
else
(if i.val < 61 then
0
else
0))
else
(if i.val < 64 then
(if i.val < 63 then
0
else
0)
else
(if i.val < 65 then
52
else
(if i.val < 66 then
0
else
57)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
0
else
0)
else
(if i.val < 70 then
0
else
0))
else
(if i.val < 73 then
(if i.val < 72 then
0
else
87)
else
(if i.val < 74 then
0
else
0)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
0
else
0)
else
(if i.val < 78 then
0
else
0))
else
(if i.val < 81 then
(if i.val < 80 then
0
else
0)
else
(if i.val < 82 then
0
else
(if i.val < 83 then
0
else
0)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
0
else
0))
else
(if i.val < 90 then
(if i.val < 89 then
36
else
33)
else
(if i.val < 91 then
0
else
57)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
0
else
0)
else
(if i.val < 95 then
52
else
0))
else
(if i.val < 98 then
(if i.val < 97 then
88
else
0)
else
(if i.val < 99 then
36
else
(if i.val < 100 then
0
else
0))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
58
else
0)
else
(if i.val < 104 then
0
else
0))
else
(if i.val < 107 then
(if i.val < 106 then
0
else
0)
else
(if i.val < 108 then
0
else
0)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
23
else
81)
else
(if i.val < 112 then
0
else
0))
else
(if i.val < 115 then
(if i.val < 114 then
0
else
0)
else
(if i.val < 116 then
139
else
(if i.val < 117 then
0
else
0)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
58
else
0)
else
(if i.val < 121 then
0
else
0))
else
(if i.val < 124 then
(if i.val < 123 then
0
else
40)
else
(if i.val < 125 then
0
else
0)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
0
else
0)
else
(if i.val < 129 then
58
else
1))
else
(if i.val < 132 then
(if i.val < 131 then
0
else
0)
else
(if i.val < 133 then
0
else
(if i.val < 134 then
86
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
0
else
0)
else
(if i.val < 138 then
0
else
0))
else
(if i.val < 141 then
(if i.val < 140 then
57
else
0)
else
(if i.val < 142 then
0
else
0)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
0
else
0)
else
(if i.val < 146 then
87
else
0))
else
(if i.val < 149 then
(if i.val < 148 then
0
else
0)
else
(if i.val < 150 then
0
else
0))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
0
else
0)
else
(if i.val < 154 then
0
else
0))
else
(if i.val < 157 then
(if i.val < 156 then
0
else
0)
else
(if i.val < 158 then
0
else
0)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
0
else
0)
else
(if i.val < 162 then
36
else
33))
else
(if i.val < 165 then
(if i.val < 164 then
0
else
57)
else
(if i.val < 166 then
0
else
(if i.val < 167 then
0
else
52))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
0
else
88)
else
(if i.val < 171 then
0
else
36))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
0)
else
(if i.val < 175 then
58
else
0)))
else
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
23
else
(if i.val < 184 then
81
else
0)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
0
else
0)
else
(if i.val < 188 then
0
else
139))
else
(if i.val < 191 then
(if i.val < 190 then
0
else
0)
else
(if i.val < 192 then
58
else
0)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
0
else
0)
else
(if i.val < 196 then
0
else
40))
else
(if i.val < 199 then
(if i.val < 198 then
0
else
0)
else
(if i.val < 200 then
0
else
(if i.val < 201 then
0
else
58)))))))
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
0
else
0))
else
(if i.val < 208 then
(if i.val < 207 then
86
else
0)
else
(if i.val < 209 then
0
else
0)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
0
else
87)
else
(if i.val < 213 then
36
else
0))
else
(if i.val < 216 then
(if i.val < 215 then
0
else
27)
else
(if i.val < 217 then
57
else
(if i.val < 218 then
0
else
60)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
33
else
35)
else
(if i.val < 222 then
136
else
64))
else
(if i.val < 225 then
(if i.val < 224 then
0
else
33)
else
(if i.val < 226 then
88
else
0)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
88
else
52)
else
(if i.val < 230 then
87
else
60))
else
(if i.val < 233 then
(if i.val < 232 then
72
else
0)
else
(if i.val < 234 then
25
else
(if i.val < 235 then
0
else
60))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
11
else
0)
else
(if i.val < 239 then
0
else
0))
else
(if i.val < 242 then
(if i.val < 241 then
0
else
58)
else
(if i.val < 243 then
0
else
0)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
27
else
0)
else
(if i.val < 247 then
0
else
0))
else
(if i.val < 250 then
(if i.val < 249 then
48
else
23)
else
(if i.val < 251 then
0
else
(if i.val < 252 then
0
else
57)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
0
else
0)
else
(if i.val < 256 then
0
else
0))
else
(if i.val < 259 then
(if i.val < 258 then
0
else
0)
else
(if i.val < 260 then
58
else
84)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
87
else
0)
else
(if i.val < 264 then
0
else
0))
else
(if i.val < 267 then
(if i.val < 266 then
40
else
0)
else
(if i.val < 268 then
0
else
(if i.val < 269 then
0
else
0)))))))))
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
0)
else
(if i.val < 273 then
0
else
0))
else
(if i.val < 276 then
(if i.val < 275 then
0
else
0)
else
(if i.val < 277 then
0
else
143)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
0
else
11)
else
(if i.val < 281 then
0
else
0))
else
(if i.val < 284 then
(if i.val < 283 then
0
else
33)
else
(if i.val < 285 then
0
else
0))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
0
else
1)
else
(if i.val < 289 then
0
else
1))
else
(if i.val < 292 then
(if i.val < 291 then
0
else
0)
else
(if i.val < 293 then
48
else
7)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
0
else
36)
else
(if i.val < 297 then
33
else
0))
else
(if i.val < 300 then
(if i.val < 299 then
57
else
0)
else
(if i.val < 301 then
0
else
(if i.val < 302 then
52
else
0))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
88
else
0)
else
(if i.val < 306 then
36
else
0))
else
(if i.val < 309 then
(if i.val < 308 then
0
else
58)
else
(if i.val < 310 then
0
else
0)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
0
else
0)
else
(if i.val < 314 then
0
else
0))
else
(if i.val < 317 then
(if i.val < 316 then
0
else
23)
else
(if i.val < 318 then
81
else
(if i.val < 319 then
0
else
0)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
0
else
0)
else
(if i.val < 323 then
139
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
0
else
58)
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
40
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
(if i.val < 336 then
58
else
1)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
0
else
0)
else
(if i.val < 340 then
0
else
86))
else
(if i.val < 343 then
(if i.val < 342 then
0
else
0)
else
(if i.val < 344 then
0
else
0)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
87
else
36)
else
(if i.val < 348 then
0
else
0))
else
(if i.val < 351 then
(if i.val < 350 then
27
else
57)
else
(if i.val < 352 then
0
else
(if i.val < 353 then
60
else
33)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
35
else
136)
else
(if i.val < 357 then
64
else
0))
else
(if i.val < 360 then
(if i.val < 359 then
33
else
88)
else
(if i.val < 361 then
0
else
88)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
52
else
87)
else
(if i.val < 365 then
60
else
72))
else
(if i.val < 368 then
(if i.val < 367 then
0
else
25)
else
(if i.val < 369 then
0
else
(if i.val < 370 then
60
else
11))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
0
else
0)
else
(if i.val < 374 then
0
else
0))
else
(if i.val < 377 then
(if i.val < 376 then
58
else
0)
else
(if i.val < 378 then
0
else
27)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
0
else
0)
else
(if i.val < 382 then
0
else
48))
else
(if i.val < 385 then
(if i.val < 384 then
23
else
0)
else
(if i.val < 386 then
0
else
(if i.val < 387 then
57
else
0)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
0
else
0)
else
(if i.val < 391 then
0
else
0))
else
(if i.val < 394 then
(if i.val < 393 then
0
else
58)
else
(if i.val < 395 then
84
else
87)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
0
else
0)
else
(if i.val < 399 then
0
else
40))
else
(if i.val < 402 then
(if i.val < 401 then
0
else
0)
else
(if i.val < 403 then
0
else
(if i.val < 404 then
0
else
0))))))))
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
0)
else
(if i.val < 408 then
0
else
0))
else
(if i.val < 411 then
(if i.val < 410 then
0
else
0)
else
(if i.val < 412 then
143
else
0)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
11
else
0)
else
(if i.val < 416 then
0
else
0))
else
(if i.val < 419 then
(if i.val < 418 then
33
else
0)
else
(if i.val < 420 then
0
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
0
else
48)
else
(if i.val < 428 then
7
else
0)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
129
else
127)
else
(if i.val < 432 then
121
else
65))
else
(if i.val < 435 then
(if i.val < 434 then
33
else
106)
else
(if i.val < 436 then
57
else
(if i.val < 437 then
33
else
129))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
88
else
88)
else
(if i.val < 441 then
139
else
0))
else
(if i.val < 444 then
(if i.val < 443 then
71
else
52)
else
(if i.val < 445 then
139
else
88)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
136
else
64)
else
(if i.val < 449 then
0
else
18))
else
(if i.val < 452 then
(if i.val < 451 then
142
else
84)
else
(if i.val < 453 then
8
else
(if i.val < 454 then
0
else
68)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
65
else
0)
else
(if i.val < 458 then
0
else
108))
else
(if i.val < 461 then
(if i.val < 460 then
59
else
41)
else
(if i.val < 462 then
106
else
88)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
107
else
0)
else
(if i.val < 466 then
52
else
0))
else
(if i.val < 469 then
(if i.val < 468 then
115
else
95)
else
(if i.val < 470 then
87
else
(if i.val < 471 then
123
else
87)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
0
else
84)
else
(if i.val < 475 then
0
else
25))
else
(if i.val < 478 then
(if i.val < 477 then
0
else
33)
else
(if i.val < 479 then
61
else
0)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
86
else
48)
else
(if i.val < 483 then
48
else
33))
else
(if i.val < 486 then
(if i.val < 485 then
55
else
0)
else
(if i.val < 487 then
0
else
(if i.val < 488 then
0
else
0)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
124
else
60)
else
(if i.val < 492 then
57
else
48))
else
(if i.val < 495 then
(if i.val < 494 then
56
else
66)
else
(if i.val < 496 then
84
else
58)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
0
else
63)
else
(if i.val < 500 then
103
else
33))
else
(if i.val < 503 then
(if i.val < 502 then
58
else
93)
else
(if i.val < 504 then
15
else
(if i.val < 505 then
98
else
84))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
126
else
0)
else
(if i.val < 509 then
0
else
0))
else
(if i.val < 512 then
(if i.val < 511 then
0
else
0)
else
(if i.val < 513 then
0
else
0)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
0
else
0)
else
(if i.val < 517 then
0
else
0))
else
(if i.val < 520 then
(if i.val < 519 then
0
else
11)
else
(if i.val < 521 then
86
else
(if i.val < 522 then
0
else
69)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
62
else
7)
else
(if i.val < 526 then
0
else
92))
else
(if i.val < 529 then
(if i.val < 528 then
47
else
73)
else
(if i.val < 530 then
21
else
0)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
1
else
36)
else
(if i.val < 534 then
11
else
92))
else
(if i.val < 537 then
(if i.val < 536 then
121
else
40)
else
(if i.val < 538 then
87
else
(if i.val < 539 then
36
else
0))))))))))
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
27)
else
(if i.val < 543 then
57
else
0))
else
(if i.val < 546 then
(if i.val < 545 then
60
else
33)
else
(if i.val < 547 then
35
else
136)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
64
else
0)
else
(if i.val < 551 then
33
else
88))
else
(if i.val < 554 then
(if i.val < 553 then
0
else
88)
else
(if i.val < 555 then
52
else
87))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
60
else
72)
else
(if i.val < 559 then
0
else
25))
else
(if i.val < 562 then
(if i.val < 561 then
0
else
60)
else
(if i.val < 563 then
11
else
0)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
0
else
0)
else
(if i.val < 567 then
0
else
58))
else
(if i.val < 570 then
(if i.val < 569 then
0
else
0)
else
(if i.val < 571 then
27
else
(if i.val < 572 then
0
else
0))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
0
else
48)
else
(if i.val < 576 then
23
else
0))
else
(if i.val < 579 then
(if i.val < 578 then
0
else
57)
else
(if i.val < 580 then
0
else
0)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
0
else
0)
else
(if i.val < 584 then
0
else
0))
else
(if i.val < 587 then
(if i.val < 586 then
58
else
84)
else
(if i.val < 588 then
87
else
(if i.val < 589 then
0
else
0)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
0
else
40)
else
(if i.val < 593 then
0
else
0))
else
(if i.val < 596 then
(if i.val < 595 then
0
else
0)
else
(if i.val < 597 then
0
else
0)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
0
else
0)
else
(if i.val < 601 then
0
else
0))
else
(if i.val < 604 then
(if i.val < 603 then
0
else
143)
else
(if i.val < 605 then
0
else
(if i.val < 606 then
11
else
0)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
0
else
0)
else
(if i.val < 610 then
33
else
0))
else
(if i.val < 613 then
(if i.val < 612 then
0
else
0)
else
(if i.val < 614 then
1
else
0)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
1
else
0)
else
(if i.val < 618 then
0
else
48))
else
(if i.val < 621 then
(if i.val < 620 then
7
else
0)
else
(if i.val < 622 then
129
else
(if i.val < 623 then
127
else
121)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
65
else
33)
else
(if i.val < 627 then
106
else
57))
else
(if i.val < 630 then
(if i.val < 629 then
33
else
129)
else
(if i.val < 631 then
88
else
88)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
139
else
0)
else
(if i.val < 635 then
71
else
52))
else
(if i.val < 638 then
(if i.val < 637 then
139
else
88)
else
(if i.val < 639 then
136
else
(if i.val < 640 then
64
else
0))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
18
else
142)
else
(if i.val < 644 then
84
else
8))
else
(if i.val < 647 then
(if i.val < 646 then
0
else
68)
else
(if i.val < 648 then
65
else
0)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
0
else
108)
else
(if i.val < 652 then
59
else
41))
else
(if i.val < 655 then
(if i.val < 654 then
106
else
88)
else
(if i.val < 656 then
107
else
(if i.val < 657 then
0
else
52)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
0
else
115)
else
(if i.val < 661 then
95
else
87))
else
(if i.val < 664 then
(if i.val < 663 then
123
else
87)
else
(if i.val < 665 then
0
else
84)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
0
else
25)
else
(if i.val < 669 then
0
else
33))
else
(if i.val < 672 then
(if i.val < 671 then
61
else
0)
else
(if i.val < 673 then
86
else
(if i.val < 674 then
48
else
48))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
33
else
55)
else
(if i.val < 678 then
0
else
0))
else
(if i.val < 681 then
(if i.val < 680 then
0
else
0)
else
(if i.val < 682 then
124
else
60)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
57
else
48)
else
(if i.val < 686 then
56
else
66))
else
(if i.val < 689 then
(if i.val < 688 then
84
else
58)
else
(if i.val < 690 then
0
else
63))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
103
else
33)
else
(if i.val < 694 then
58
else
93))
else
(if i.val < 697 then
(if i.val < 696 then
15
else
98)
else
(if i.val < 698 then
84
else
126)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
0
else
0)
else
(if i.val < 702 then
0
else
0))
else
(if i.val < 705 then
(if i.val < 704 then
0
else
0)
else
(if i.val < 706 then
0
else
(if i.val < 707 then
0
else
0))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
0
else
0)
else
(if i.val < 711 then
0
else
11))
else
(if i.val < 714 then
(if i.val < 713 then
86
else
0)
else
(if i.val < 715 then
69
else
62)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
7
else
0)
else
(if i.val < 719 then
92
else
47))
else
(if i.val < 722 then
(if i.val < 721 then
73
else
21)
else
(if i.val < 723 then
0
else
(if i.val < 724 then
1
else
36)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
11
else
92)
else
(if i.val < 728 then
121
else
40))
else
(if i.val < 731 then
(if i.val < 730 then
67
else
106)
else
(if i.val < 732 then
127
else
121)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
0
else
57)
else
(if i.val < 736 then
57
else
71))
else
(if i.val < 739 then
(if i.val < 738 then
0
else
47)
else
(if i.val < 740 then
136
else
(if i.val < 741 then
64
else
136)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
142
else
55)
else
(if i.val < 745 then
33
else
104))
else
(if i.val < 748 then
(if i.val < 747 then
61
else
27)
else
(if i.val < 749 then
130
else
88)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
137
else
76)
else
(if i.val < 753 then
34
else
129))
else
(if i.val < 756 then
(if i.val < 755 then
63
else
62)
else
(if i.val < 757 then
60
else
(if i.val < 758 then
87
else
0)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
1
else
16)
else
(if i.val < 762 then
56
else
0))
else
(if i.val < 765 then
(if i.val < 764 then
0
else
91)
else
(if i.val < 766 then
136
else
40)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
0
else
10)
else
(if i.val < 770 then
0
else
124))
else
(if i.val < 773 then
(if i.val < 772 then
90
else
18)
else
(if i.val < 774 then
82
else
(if i.val < 775 then
32
else
83))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
10)
else
(if i.val < 779 then
8
else
47))
else
(if i.val < 782 then
(if i.val < 781 then
106
else
87)
else
(if i.val < 783 then
126
else
75)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
55
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
35
else
11)
else
(if i.val < 791 then
0
else
(if i.val < 792 then
48
else
0)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
0
else
136)
else
(if i.val < 796 then
129
else
127))
else
(if i.val < 799 then
(if i.val < 798 then
121
else
65)
else
(if i.val < 800 then
33
else
106)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
57
else
33)
else
(if i.val < 804 then
129
else
88))
else
(if i.val < 807 then
(if i.val < 806 then
88
else
139)
else
(if i.val < 808 then
0
else
(if i.val < 809 then
71
else
52)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
139
else
88)
else
(if i.val < 813 then
136
else
64))
else
(if i.val < 816 then
(if i.val < 815 then
0
else
18)
else
(if i.val < 817 then
142
else
84)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
8
else
0)
else
(if i.val < 821 then
68
else
65))
else
(if i.val < 824 then
(if i.val < 823 then
0
else
0)
else
(if i.val < 825 then
108
else
59))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
41
else
106)
else
(if i.val < 829 then
88
else
107))
else
(if i.val < 832 then
(if i.val < 831 then
0
else
52)
else
(if i.val < 833 then
0
else
115)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
95
else
87)
else
(if i.val < 837 then
123
else
87))
else
(if i.val < 840 then
(if i.val < 839 then
0
else
84)
else
(if i.val < 841 then
0
else
(if i.val < 842 then
25
else
0))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
33
else
61)
else
(if i.val < 846 then
0
else
86))
else
(if i.val < 849 then
(if i.val < 848 then
48
else
48)
else
(if i.val < 850 then
33
else
55)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
0
else
0)
else
(if i.val < 854 then
0
else
0))
else
(if i.val < 857 then
(if i.val < 856 then
124
else
60)
else
(if i.val < 858 then
57
else
(if i.val < 859 then
48
else
56)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
66
else
84)
else
(if i.val < 863 then
58
else
0))
else
(if i.val < 866 then
(if i.val < 865 then
63
else
103)
else
(if i.val < 867 then
33
else
58)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
93
else
15)
else
(if i.val < 871 then
98
else
84))
else
(if i.val < 874 then
(if i.val < 873 then
126
else
0)
else
(if i.val < 875 then
0
else
(if i.val < 876 then
0
else
0)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
0
else
0)
else
(if i.val < 880 then
0
else
0))
else
(if i.val < 883 then
(if i.val < 882 then
0
else
0)
else
(if i.val < 884 then
0
else
0)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
11
else
86)
else
(if i.val < 888 then
0
else
69))
else
(if i.val < 891 then
(if i.val < 890 then
62
else
7)
else
(if i.val < 892 then
0
else
(if i.val < 893 then
92
else
47)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
73
else
21)
else
(if i.val < 897 then
0
else
1))
else
(if i.val < 900 then
(if i.val < 899 then
36
else
11)
else
(if i.val < 901 then
92
else
121)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
40
else
67)
else
(if i.val < 905 then
106
else
127))
else
(if i.val < 908 then
(if i.val < 907 then
121
else
0)
else
(if i.val < 909 then
57
else
(if i.val < 910 then
57
else
71))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
0
else
47)
else
(if i.val < 914 then
136
else
64))
else
(if i.val < 917 then
(if i.val < 916 then
136
else
142)
else
(if i.val < 918 then
55
else
33)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
104
else
61)
else
(if i.val < 922 then
27
else
130))
else
(if i.val < 925 then
(if i.val < 924 then
88
else
137)
else
(if i.val < 926 then
76
else
(if i.val < 927 then
34
else
129)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
63
else
62)
else
(if i.val < 931 then
60
else
87))
else
(if i.val < 934 then
(if i.val < 933 then
0
else
1)
else
(if i.val < 935 then
16
else
56)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
0)
else
(if i.val < 939 then
91
else
136))
else
(if i.val < 942 then
(if i.val < 941 then
40
else
0)
else
(if i.val < 943 then
10
else
(if i.val < 944 then
0
else
124))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
90
else
18)
else
(if i.val < 948 then
82
else
32))
else
(if i.val < 951 then
(if i.val < 950 then
83
else
0)
else
(if i.val < 952 then
10
else
8)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
47
else
106)
else
(if i.val < 956 then
87
else
126))
else
(if i.val < 959 then
(if i.val < 958 then
75
else
55)
else
(if i.val < 960 then
0
else
0))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
0
else
35)
else
(if i.val < 964 then
11
else
0))
else
(if i.val < 967 then
(if i.val < 966 then
48
else
0)
else
(if i.val < 968 then
0
else
136)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
93
else
67)
else
(if i.val < 972 then
129
else
36))
else
(if i.val < 975 then
(if i.val < 974 then
142
else
8)
else
(if i.val < 976 then
33
else
(if i.val < 977 then
122
else
90))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
72
else
100)
else
(if i.val < 981 then
91
else
71))
else
(if i.val < 984 then
(if i.val < 983 then
92
else
51)
else
(if i.val < 985 then
67
else
106)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
127
else
121)
else
(if i.val < 989 then
0
else
57))
else
(if i.val < 992 then
(if i.val < 991 then
57
else
71)
else
(if i.val < 993 then
0
else
(if i.val < 994 then
47
else
136)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
64
else
136)
else
(if i.val < 998 then
142
else
55))
else
(if i.val < 1001 then
(if i.val < 1000 then
33
else
104)
else
(if i.val < 1002 then
61
else
27)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
130
else
88)
else
(if i.val < 1006 then
137
else
76))
else
(if i.val < 1009 then
(if i.val < 1008 then
34
else
129)
else
(if i.val < 1010 then
63
else
(if i.val < 1011 then
62
else
60)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
87
else
0)
else
(if i.val < 1015 then
1
else
16))
else
(if i.val < 1018 then
(if i.val < 1017 then
56
else
0)
else
(if i.val < 1019 then
0
else
91)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
136
else
40)
else
(if i.val < 1023 then
0
else
10))
else
(if i.val < 1026 then
(if i.val < 1025 then
0
else
124)
else
(if i.val < 1027 then
90
else
(if i.val < 1028 then
18
else
82)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
32
else
83)
else
(if i.val < 1032 then
0
else
10))
else
(if i.val < 1035 then
(if i.val < 1034 then
8
else
47)
else
(if i.val < 1036 then
106
else
87)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
126
else
75)
else
(if i.val < 1040 then
55
else
0))
else
(if i.val < 1043 then
(if i.val < 1042 then
0
else
0)
else
(if i.val < 1044 then
35
else
(if i.val < 1045 then
11
else
0))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
48
else
0)
else
(if i.val < 1049 then
0
else
136))
else
(if i.val < 1052 then
(if i.val < 1051 then
93
else
67)
else
(if i.val < 1053 then
129
else
36)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
142
else
8)
else
(if i.val < 1057 then
33
else
122))
else
(if i.val < 1060 then
(if i.val < 1059 then
90
else
72)
else
(if i.val < 1061 then
100
else
(if i.val < 1062 then
91
else
71)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
92
else
51)
else
(if i.val < 1066 then
93
else
67))
else
(if i.val < 1069 then
(if i.val < 1068 then
129
else
36)
else
(if i.val < 1070 then
142
else
8)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
33
else
122)
else
(if i.val < 1074 then
90
else
72))
else
(if i.val < 1077 then
(if i.val < 1076 then
100
else
91)
else
(if i.val < 1078 then
71
else
(if i.val < 1079 then
92
else
51)))))))))))

def g32p_row06_cosetGeneratorFactorColumn3 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 540 then
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
68)))
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
36))
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
2)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
56
else
0)
else
(if i.val < 27 then
92
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
68
else
(if i.val < 32 then
0
else
0))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
68
else
0)
else
(if i.val < 36 then
0
else
0))
else
(if i.val < 39 then
(if i.val < 38 then
0
else
0)
else
(if i.val < 40 then
0
else
0)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
0
else
19)
else
(if i.val < 44 then
0
else
0))
else
(if i.val < 47 then
(if i.val < 46 then
0
else
0)
else
(if i.val < 48 then
68
else
(if i.val < 49 then
0
else
0)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
0
else
58)
else
(if i.val < 53 then
0
else
0))
else
(if i.val < 56 then
(if i.val < 55 then
0
else
2)
else
(if i.val < 57 then
7
else
19)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
65
else
87)
else
(if i.val < 61 then
23
else
0))
else
(if i.val < 64 then
(if i.val < 63 then
0
else
68)
else
(if i.val < 65 then
0
else
(if i.val < 66 then
0
else
56)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
0
else
0)
else
(if i.val < 70 then
2
else
2))
else
(if i.val < 73 then
(if i.val < 72 then
19
else
88)
else
(if i.val < 74 then
62
else
0)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
56
else
0)
else
(if i.val < 78 then
68
else
11))
else
(if i.val < 81 then
(if i.val < 80 then
0
else
0)
else
(if i.val < 82 then
0
else
(if i.val < 83 then
0
else
36)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
92
else
0)
else
(if i.val < 87 then
0
else
68))
else
(if i.val < 90 then
(if i.val < 89 then
36
else
0)
else
(if i.val < 91 then
0
else
129)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
0
else
68)
else
(if i.val < 95 then
0
else
0))
else
(if i.val < 98 then
(if i.val < 97 then
68
else
0)
else
(if i.val < 99 then
0
else
(if i.val < 100 then
0
else
2))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
0
else
0)
else
(if i.val < 104 then
0
else
0))
else
(if i.val < 107 then
(if i.val < 106 then
0
else
0)
else
(if i.val < 108 then
0
else
33)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
0
else
0)
else
(if i.val < 112 then
0
else
0))
else
(if i.val < 115 then
(if i.val < 114 then
0
else
0)
else
(if i.val < 116 then
86
else
(if i.val < 117 then
57
else
0)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
0
else
121)
else
(if i.val < 121 then
0
else
0))
else
(if i.val < 124 then
(if i.val < 123 then
0
else
1)
else
(if i.val < 125 then
1
else
36)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
0
else
68)
else
(if i.val < 129 then
0
else
43))
else
(if i.val < 132 then
(if i.val < 131 then
0
else
0)
else
(if i.val < 133 then
0
else
(if i.val < 134 then
43
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
0
else
0)
else
(if i.val < 138 then
0
else
0))
else
(if i.val < 141 then
(if i.val < 140 then
2
else
2)
else
(if i.val < 142 then
7
else
2)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
2
else
19)
else
(if i.val < 146 then
87
else
60))
else
(if i.val < 149 then
(if i.val < 148 then
68
else
56)
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
11
else
0)
else
(if i.val < 154 then
52
else
0))
else
(if i.val < 157 then
(if i.val < 156 then
0
else
65)
else
(if i.val < 158 then
0
else
0)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
0
else
43)
else
(if i.val < 162 then
2
else
56))
else
(if i.val < 165 then
(if i.val < 164 then
0
else
43)
else
(if i.val < 166 then
0
else
(if i.val < 167 then
56
else
56))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
36
else
0)
else
(if i.val < 171 then
65
else
2))
else
(if i.val < 174 then
(if i.val < 173 then
0
else
2)
else
(if i.val < 175 then
2
else
43)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
0)
else
(if i.val < 179 then
62
else
0))
else
(if i.val < 182 then
(if i.val < 181 then
2
else
19)
else
(if i.val < 183 then
88
else
(if i.val < 184 then
0
else
0)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
136
else
26)
else
(if i.val < 188 then
2
else
86))
else
(if i.val < 191 then
(if i.val < 190 then
11
else
138)
else
(if i.val < 192 then
136
else
56)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
69
else
0)
else
(if i.val < 196 then
52
else
11))
else
(if i.val < 199 then
(if i.val < 198 then
11
else
11)
else
(if i.val < 200 then
0
else
(if i.val < 201 then
0
else
68)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
0
else
0)
else
(if i.val < 205 then
23
else
0))
else
(if i.val < 208 then
(if i.val < 207 then
68
else
0)
else
(if i.val < 209 then
0
else
36)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
0
else
19)
else
(if i.val < 213 then
87
else
139))
else
(if i.val < 216 then
(if i.val < 215 then
68
else
0)
else
(if i.val < 217 then
68
else
(if i.val < 218 then
55
else
0)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
0
else
0)
else
(if i.val < 222 then
36
else
92))
else
(if i.val < 225 then
(if i.val < 224 then
0
else
0)
else
(if i.val < 226 then
0
else
0)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
68
else
0)
else
(if i.val < 230 then
0
else
1))
else
(if i.val < 233 then
(if i.val < 232 then
0
else
40)
else
(if i.val < 234 then
108
else
(if i.val < 235 then
0
else
33))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
104
else
0)
else
(if i.val < 239 then
93
else
86))
else
(if i.val < 242 then
(if i.val < 241 then
48
else
0)
else
(if i.val < 243 then
121
else
76)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
0
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
36
else
0)
else
(if i.val < 251 then
43
else
(if i.val < 252 then
0
else
27)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
43
else
0)
else
(if i.val < 256 then
0
else
0))
else
(if i.val < 259 then
(if i.val < 258 then
0
else
16)
else
(if i.val < 260 then
0
else
83)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
1
else
93)
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
57)
else
(if i.val < 268 then
0
else
(if i.val < 269 then
5
else
136)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
52
else
81)
else
(if i.val < 273 then
115
else
0))
else
(if i.val < 276 then
(if i.val < 275 then
0
else
0)
else
(if i.val < 277 then
43
else
0)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
0
else
0)
else
(if i.val < 281 then
52
else
1))
else
(if i.val < 284 then
(if i.val < 283 then
68
else
0)
else
(if i.val < 285 then
0
else
0))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
40
else
9)
else
(if i.val < 289 then
93
else
26))
else
(if i.val < 292 then
(if i.val < 291 then
108
else
36)
else
(if i.val < 293 then
7
else
0)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
0
else
0)
else
(if i.val < 297 then
19
else
65))
else
(if i.val < 300 then
(if i.val < 299 then
71
else
19)
else
(if i.val < 301 then
2
else
(if i.val < 302 then
2
else
7))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
52
else
125)
else
(if i.val < 306 then
127
else
89))
else
(if i.val < 309 then
(if i.val < 308 then
2
else
48)
else
(if i.val < 310 then
19
else
89)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
5
else
56)
else
(if i.val < 314 then
0
else
68))
else
(if i.val < 317 then
(if i.val < 316 then
19
else
84)
else
(if i.val < 318 then
0
else
(if i.val < 319 then
73
else
62)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
40
else
126)
else
(if i.val < 323 then
86
else
50))
else
(if i.val < 326 then
(if i.val < 325 then
19
else
63)
else
(if i.val < 327 then
36
else
116)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
11
else
136)
else
(if i.val < 331 then
11
else
11))
else
(if i.val < 334 then
(if i.val < 333 then
36
else
0)
else
(if i.val < 335 then
52
else
(if i.val < 336 then
43
else
68)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
0
else
0)
else
(if i.val < 340 then
0
else
115))
else
(if i.val < 343 then
(if i.val < 342 then
91
else
0)
else
(if i.val < 344 then
36
else
0)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
2
else
43)
else
(if i.val < 348 then
56
else
56))
else
(if i.val < 351 then
(if i.val < 350 then
26
else
43)
else
(if i.val < 352 then
55
else
(if i.val < 353 then
0
else
27)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
0
else
2)
else
(if i.val < 357 then
19
else
88))
else
(if i.val < 360 then
(if i.val < 359 then
26
else
19)
else
(if i.val < 361 then
65
else
102)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
68
else
87)
else
(if i.val < 365 then
27
else
11))
else
(if i.val < 368 then
(if i.val < 367 then
60
else
36)
else
(if i.val < 369 then
0
else
(if i.val < 370 then
88
else
2))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
0
else
26)
else
(if i.val < 374 then
86
else
52))
else
(if i.val < 377 then
(if i.val < 376 then
0
else
56)
else
(if i.val < 378 then
69
else
0)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
102
else
36)
else
(if i.val < 382 then
43
else
0))
else
(if i.val < 385 then
(if i.val < 384 then
62
else
56)
else
(if i.val < 386 then
0
else
(if i.val < 387 then
88
else
43)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
0
else
0)
else
(if i.val < 391 then
2
else
88))
else
(if i.val < 394 then
(if i.val < 393 then
0
else
136)
else
(if i.val < 395 then
22
else
66)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
26
else
55)
else
(if i.val < 399 then
55
else
11))
else
(if i.val < 402 then
(if i.val < 401 then
86
else
138)
else
(if i.val < 403 then
127
else
(if i.val < 404 then
136
else
119))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
81
else
26)
else
(if i.val < 408 then
41
else
136))
else
(if i.val < 411 then
(if i.val < 410 then
68
else
38)
else
(if i.val < 412 then
52
else
0)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
52
else
52)
else
(if i.val < 416 then
0
else
11))
else
(if i.val < 419 then
(if i.val < 418 then
0
else
0)
else
(if i.val < 420 then
7
else
0))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
0
else
136)
else
(if i.val < 424 then
26
else
2))
else
(if i.val < 427 then
(if i.val < 426 then
69
else
0)
else
(if i.val < 428 then
23
else
0)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
56
else
56)
else
(if i.val < 432 then
1
else
140))
else
(if i.val < 435 then
(if i.val < 434 then
52
else
0)
else
(if i.val < 436 then
125
else
(if i.val < 437 then
0
else
0))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
125
else
26)
else
(if i.val < 441 then
86
else
55))
else
(if i.val < 444 then
(if i.val < 443 then
55
else
136)
else
(if i.val < 445 then
56
else
52)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
138
else
138)
else
(if i.val < 449 then
55
else
0))
else
(if i.val < 452 then
(if i.val < 451 then
23
else
69)
else
(if i.val < 453 then
0
else
(if i.val < 454 then
36
else
139)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
68
else
68)
else
(if i.val < 458 then
0
else
0))
else
(if i.val < 461 then
(if i.val < 460 then
36
else
0)
else
(if i.val < 462 then
0
else
86)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
1
else
48)
else
(if i.val < 466 then
0
else
72))
else
(if i.val < 469 then
(if i.val < 468 then
139
else
43)
else
(if i.val < 470 then
108
else
(if i.val < 471 then
27
else
43)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
40
else
0)
else
(if i.val < 475 then
68
else
1))
else
(if i.val < 478 then
(if i.val < 477 then
1
else
5)
else
(if i.val < 479 then
125
else
48)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
68
else
33)
else
(if i.val < 483 then
43
else
0))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
52)
else
(if i.val < 487 then
47
else
(if i.val < 488 then
0
else
0)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
0
else
40)
else
(if i.val < 492 then
108
else
7))
else
(if i.val < 495 then
(if i.val < 494 then
58
else
0)
else
(if i.val < 496 then
105
else
1)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
86
else
1)
else
(if i.val < 500 then
86
else
33))
else
(if i.val < 503 then
(if i.val < 502 then
16
else
0)
else
(if i.val < 504 then
1
else
(if i.val < 505 then
1
else
57))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
142
else
0)
else
(if i.val < 509 then
52
else
63))
else
(if i.val < 512 then
(if i.val < 511 then
121
else
141)
else
(if i.val < 513 then
115
else
48)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
0
else
43)
else
(if i.val < 517 then
43
else
7))
else
(if i.val < 520 then
(if i.val < 519 then
1
else
0)
else
(if i.val < 521 then
136
else
(if i.val < 522 then
35
else
0)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
11
else
40)
else
(if i.val < 526 then
0
else
43))
else
(if i.val < 529 then
(if i.val < 528 then
40
else
48)
else
(if i.val < 530 then
40
else
40)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
27
else
7)
else
(if i.val < 534 then
143
else
36))
else
(if i.val < 537 then
(if i.val < 536 then
0
else
0)
else
(if i.val < 538 then
2
else
(if i.val < 539 then
124
else
56))))))))))
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
56
else
26)
else
(if i.val < 543 then
56
else
0))
else
(if i.val < 546 then
(if i.val < 545 then
132
else
124)
else
(if i.val < 547 then
36
else
19)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
58
else
2)
else
(if i.val < 551 then
26
else
52))
else
(if i.val < 554 then
(if i.val < 553 then
104
else
2)
else
(if i.val < 555 then
48
else
7))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
27
else
11)
else
(if i.val < 559 then
60
else
91))
else
(if i.val < 562 then
(if i.val < 561 then
0
else
58)
else
(if i.val < 563 then
2
else
0)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
84
else
86)
else
(if i.val < 567 then
2
else
47))
else
(if i.val < 570 then
(if i.val < 569 then
35
else
7)
else
(if i.val < 571 then
2
else
(if i.val < 572 then
56
else
33))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
124
else
50)
else
(if i.val < 576 then
84
else
43))
else
(if i.val < 579 then
(if i.val < 578 then
0
else
88)
else
(if i.val < 580 then
115
else
133)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
0
else
48)
else
(if i.val < 584 then
9
else
84))
else
(if i.val < 587 then
(if i.val < 586 then
136
else
84)
else
(if i.val < 588 then
66
else
(if i.val < 589 then
139
else
76)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
86
else
138)
else
(if i.val < 593 then
81
else
48))
else
(if i.val < 596 then
(if i.val < 595 then
142
else
136)
else
(if i.val < 597 then
111
else
76)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
136
else
63)
else
(if i.val < 601 then
136
else
119))
else
(if i.val < 604 then
(if i.val < 603 then
103
else
11)
else
(if i.val < 605 then
0
else
(if i.val < 606 then
68
else
52)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
52
else
58)
else
(if i.val < 610 then
40
else
0))
else
(if i.val < 613 then
(if i.val < 612 then
89
else
91)
else
(if i.val < 614 then
0
else
83)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
115
else
128)
else
(if i.val < 618 then
118
else
38))
else
(if i.val < 621 then
(if i.val < 620 then
40
else
0)
else
(if i.val < 622 then
2
else
(if i.val < 623 then
2
else
43)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
127
else
52)
else
(if i.val < 627 then
11
else
26))
else
(if i.val < 630 then
(if i.val < 629 then
56
else
26)
else
(if i.val < 631 then
125
else
26)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
86
else
18)
else
(if i.val < 635 then
52
else
136))
else
(if i.val < 638 then
(if i.val < 637 then
56
else
102)
else
(if i.val < 639 then
138
else
(if i.val < 640 then
55
else
55))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
56
else
88)
else
(if i.val < 644 then
34
else
0))
else
(if i.val < 647 then
(if i.val < 646 then
127
else
68)
else
(if i.val < 648 then
56
else
43)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
73
else
65)
else
(if i.val < 652 then
65
else
63))
else
(if i.val < 655 then
(if i.val < 654 then
133
else
26)
else
(if i.val < 656 then
86
else
(if i.val < 657 then
50
else
7)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
11
else
2)
else
(if i.val < 661 then
19
else
65))
else
(if i.val < 664 then
(if i.val < 663 then
27
else
87)
else
(if i.val < 665 then
11
else
0)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
68
else
36)
else
(if i.val < 669 then
41
else
32))
else
(if i.val < 672 then
(if i.val < 671 then
141
else
102)
else
(if i.val < 673 then
56
else
(if i.val < 674 then
0
else
19))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
136
else
27)
else
(if i.val < 678 then
102
else
26))
else
(if i.val < 681 then
(if i.val < 680 then
0
else
34)
else
(if i.val < 682 then
0
else
0)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
88
else
0)
else
(if i.val < 686 then
68
else
33))
else
(if i.val < 689 then
(if i.val < 688 then
69
else
136)
else
(if i.val < 690 then
86
else
41))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
86
else
55)
else
(if i.val < 694 then
136
else
138))
else
(if i.val < 697 then
(if i.val < 696 then
29
else
125)
else
(if i.val < 698 then
57
else
11)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
127
else
11)
else
(if i.val < 702 then
63
else
62))
else
(if i.val < 705 then
(if i.val < 704 then
11
else
56)
else
(if i.val < 706 then
92
else
(if i.val < 707 then
68
else
121))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
78
else
52)
else
(if i.val < 711 then
11
else
52))
else
(if i.val < 714 then
(if i.val < 713 then
136
else
55)
else
(if i.val < 715 then
136
else
11)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
0
else
0)
else
(if i.val < 719 then
58
else
0))
else
(if i.val < 722 then
(if i.val < 721 then
52
else
89)
else
(if i.val < 723 then
5
else
(if i.val < 724 then
73
else
11)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
52
else
41)
else
(if i.val < 728 then
0
else
7))
else
(if i.val < 731 then
(if i.val < 730 then
0
else
56)
else
(if i.val < 732 then
51
else
111)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
34
else
68)
else
(if i.val < 736 then
0
else
136))
else
(if i.val < 739 then
(if i.val < 738 then
66
else
26)
else
(if i.val < 740 then
86
else
(if i.val < 741 then
55
else
114)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
11
else
52)
else
(if i.val < 745 then
11
else
11))
else
(if i.val < 748 then
(if i.val < 747 then
26
else
27)
else
(if i.val < 749 then
30
else
26)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
138
else
56)
else
(if i.val < 753 then
52
else
0))
else
(if i.val < 756 then
(if i.val < 755 then
36
else
43)
else
(if i.val < 757 then
33
else
(if i.val < 758 then
48
else
9)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
54
else
91)
else
(if i.val < 762 then
81
else
35))
else
(if i.val < 765 then
(if i.val < 764 then
94
else
48)
else
(if i.val < 766 then
40
else
142)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
68
else
141)
else
(if i.val < 770 then
116
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
43
else
(if i.val < 775 then
9
else
84))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
71
else
83)
else
(if i.val < 779 then
60
else
0))
else
(if i.val < 782 then
(if i.val < 781 then
125
else
78)
else
(if i.val < 783 then
92
else
76)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
48
else
143)
else
(if i.val < 787 then
119
else
112))
else
(if i.val < 790 then
(if i.val < 789 then
136
else
29)
else
(if i.val < 791 then
0
else
(if i.val < 792 then
47
else
7)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
33
else
26)
else
(if i.val < 796 then
56
else
127))
else
(if i.val < 799 then
(if i.val < 798 then
48
else
138)
else
(if i.val < 800 then
60
else
11)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
56
else
56)
else
(if i.val < 804 then
26
else
125))
else
(if i.val < 807 then
(if i.val < 806 then
26
else
0)
else
(if i.val < 808 then
57
else
(if i.val < 809 then
50
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
56
else
2)
else
(if i.val < 813 then
1
else
0))
else
(if i.val < 816 then
(if i.val < 815 then
60
else
84)
else
(if i.val < 817 then
71
else
11)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
36
else
19)
else
(if i.val < 821 then
40
else
2))
else
(if i.val < 824 then
(if i.val < 823 then
7
else
52)
else
(if i.val < 825 then
65
else
0))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
133
else
71)
else
(if i.val < 829 then
60
else
7))
else
(if i.val < 832 then
(if i.val < 831 then
47
else
25)
else
(if i.val < 833 then
1
else
62)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
16
else
104)
else
(if i.val < 837 then
123
else
58))
else
(if i.val < 840 then
(if i.val < 839 then
11
else
0)
else
(if i.val < 841 then
68
else
(if i.val < 842 then
19
else
41))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
97
else
125)
else
(if i.val < 846 then
2
else
2))
else
(if i.val < 849 then
(if i.val < 848 then
47
else
19)
else
(if i.val < 850 then
89
else
21)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
80
else
48)
else
(if i.val < 854 then
40
else
56))
else
(if i.val < 857 then
(if i.val < 856 then
0
else
47)
else
(if i.val < 858 then
59
else
(if i.val < 859 then
71
else
127)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
84
else
101)
else
(if i.val < 863 then
48
else
86))
else
(if i.val < 866 then
(if i.val < 865 then
41
else
76)
else
(if i.val < 867 then
21
else
138)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
136
else
29)
else
(if i.val < 871 then
47
else
81))
else
(if i.val < 874 then
(if i.val < 873 then
7
else
127)
else
(if i.val < 875 then
141
else
(if i.val < 876 then
89
else
136)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
141
else
136)
else
(if i.val < 880 then
83
else
143))
else
(if i.val < 883 then
(if i.val < 882 then
52
else
103)
else
(if i.val < 884 then
82
else
68)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
52
else
136)
else
(if i.val < 888 then
35
else
63))
else
(if i.val < 891 then
(if i.val < 890 then
11
else
91)
else
(if i.val < 892 then
0
else
(if i.val < 893 then
43
else
0)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
68
else
50)
else
(if i.val < 897 then
133
else
0))
else
(if i.val < 900 then
(if i.val < 899 then
38
else
68)
else
(if i.val < 901 then
119
else
0)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
76
else
36)
else
(if i.val < 905 then
11
else
127))
else
(if i.val < 908 then
(if i.val < 907 then
131
else
63)
else
(if i.val < 909 then
56
else
(if i.val < 910 then
26
else
136))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
26
else
90)
else
(if i.val < 914 then
82
else
136))
else
(if i.val < 917 then
(if i.val < 916 then
114
else
63)
else
(if i.val < 918 then
129
else
124)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
141
else
34)
else
(if i.val < 922 then
133
else
69))
else
(if i.val < 925 then
(if i.val < 924 then
131
else
138)
else
(if i.val < 926 then
56
else
(if i.val < 927 then
136
else
102)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
63
else
121)
else
(if i.val < 931 then
7
else
73))
else
(if i.val < 934 then
(if i.val < 933 then
60
else
36)
else
(if i.val < 935 then
5
else
82)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
136
else
94)
else
(if i.val < 939 then
51
else
38))
else
(if i.val < 942 then
(if i.val < 941 then
142
else
102)
else
(if i.val < 943 then
141
else
(if i.val < 944 then
136
else
94))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
27
else
11)
else
(if i.val < 948 then
43
else
56))
else
(if i.val < 951 then
(if i.val < 950 then
132
else
23)
else
(if i.val < 952 then
33
else
34)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
0
else
2)
else
(if i.val < 956 then
85
else
16))
else
(if i.val < 959 then
(if i.val < 958 then
29
else
52)
else
(if i.val < 960 then
52
else
63))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
2
else
68)
else
(if i.val < 964 then
29
else
0))
else
(if i.val < 967 then
(if i.val < 966 then
47
else
2)
else
(if i.val < 968 then
33
else
127)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
90
else
94)
else
(if i.val < 972 then
114
else
121))
else
(if i.val < 975 then
(if i.val < 974 then
52
else
0)
else
(if i.val < 976 then
7
else
(if i.val < 977 then
48
else
0))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
42
else
40)
else
(if i.val < 981 then
25
else
66))
else
(if i.val < 984 then
(if i.val < 983 then
8
else
47)
else
(if i.val < 985 then
141
else
141)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
124
else
68)
else
(if i.val < 989 then
63
else
2))
else
(if i.val < 992 then
(if i.val < 991 then
84
else
125)
else
(if i.val < 993 then
136
else
(if i.val < 994 then
26
else
36)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
136
else
54)
else
(if i.val < 998 then
124
else
5))
else
(if i.val < 1001 then
(if i.val < 1000 then
1
else
11)
else
(if i.val < 1002 then
34
else
100)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
133
else
60)
else
(if i.val < 1006 then
138
else
1))
else
(if i.val < 1009 then
(if i.val < 1008 then
5
else
34)
else
(if i.val < 1010 then
133
else
(if i.val < 1011 then
21
else
5)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
84
else
60)
else
(if i.val < 1015 then
30
else
134))
else
(if i.val < 1018 then
(if i.val < 1017 then
101
else
35)
else
(if i.val < 1019 then
94
else
38)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
19
else
142)
else
(if i.val < 1023 then
68
else
141))
else
(if i.val < 1026 then
(if i.val < 1025 then
89
else
94)
else
(if i.val < 1027 then
124
else
(if i.val < 1028 then
56
else
54)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
71
else
47)
else
(if i.val < 1032 then
84
else
21))
else
(if i.val < 1035 then
(if i.val < 1034 then
84
else
0)
else
(if i.val < 1036 then
81
else
130)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
48
else
29)
else
(if i.val < 1040 then
50
else
119))
else
(if i.val < 1043 then
(if i.val < 1042 then
119
else
115)
else
(if i.val < 1044 then
2
else
(if i.val < 1045 then
29
else
0))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
47
else
71)
else
(if i.val < 1049 then
33
else
71))
else
(if i.val < 1052 then
(if i.val < 1051 then
2
else
94)
else
(if i.val < 1053 then
79
else
56)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
63
else
11)
else
(if i.val < 1057 then
0
else
52))
else
(if i.val < 1060 then
(if i.val < 1059 then
36
else
132)
else
(if i.val < 1061 then
72
else
(if i.val < 1062 then
29
else
94)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
0
else
9)
else
(if i.val < 1066 then
90
else
94))
else
(if i.val < 1069 then
(if i.val < 1068 then
82
else
141)
else
(if i.val < 1070 then
65
else
84)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
36
else
1)
else
(if i.val < 1074 then
141
else
42))
else
(if i.val < 1077 then
(if i.val < 1076 then
92
else
6)
else
(if i.val < 1078 then
136
else
(if i.val < 1079 then
36
else
27)))))))))))

def g32p_row06_cosetGeneratorFactor : Fin 4 → Fin 1080 → Fin 144 :=
  ![g32p_row06_cosetGeneratorFactorColumn0, g32p_row06_cosetGeneratorFactorColumn1, g32p_row06_cosetGeneratorFactorColumn2, g32p_row06_cosetGeneratorFactorColumn3]

def g32p_row06_cosetBranchNextColumn0 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
634
else
930)
else
(if i.val < 3 then
872
else
900))
else
(if i.val < 6 then
(if i.val < 5 then
197
else
362)
else
(if i.val < 7 then
423
else
1052)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
369
else
501)
else
(if i.val < 11 then
374
else
415))
else
(if i.val < 14 then
(if i.val < 13 then
446
else
437)
else
(if i.val < 15 then
1031
else
407))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
387
else
1045)
else
(if i.val < 19 then
342
else
607))
else
(if i.val < 22 then
(if i.val < 21 then
658
else
568)
else
(if i.val < 23 then
565
else
659)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
779
else
663)
else
(if i.val < 27 then
544
else
730))
else
(if i.val < 30 then
(if i.val < 29 then
621
else
1)
else
(if i.val < 31 then
84
else
(if i.val < 32 then
583
else
541))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
671
else
548)
else
(if i.val < 36 then
722
else
599))
else
(if i.val < 39 then
(if i.val < 38 then
81
else
707)
else
(if i.val < 40 then
602
else
741)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
120
else
1079)
else
(if i.val < 44 then
735
else
666))
else
(if i.val < 47 then
(if i.val < 46 then
106
else
83)
else
(if i.val < 48 then
694
else
(if i.val < 49 then
1075
else
592)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
723
else
609)
else
(if i.val < 53 then
682
else
127))
else
(if i.val < 56 then
(if i.val < 55 then
606
else
811)
else
(if i.val < 57 then
282
else
6)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
260
else
881)
else
(if i.val < 61 then
171
else
142))
else
(if i.val < 64 then
(if i.val < 63 then
228
else
876)
else
(if i.val < 65 then
806
else
(if i.val < 66 then
873
else
941)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
193
else
797)
else
(if i.val < 70 then
907
else
173))
else
(if i.val < 73 then
(if i.val < 72 then
234
else
159)
else
(if i.val < 74 then
946
else
804)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
892
else
146)
else
(if i.val < 78 then
891
else
217))
else
(if i.val < 81 then
(if i.val < 80 then
827
else
7)
else
(if i.val < 82 then
198
else
(if i.val < 83 then
899
else
244)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
206
else
181)
else
(if i.val < 87 then
145
else
814))
else
(if i.val < 90 then
(if i.val < 89 then
846
else
810)
else
(if i.val < 91 then
268
else
152)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
9
else
222)
else
(if i.val < 95 then
813
else
796))
else
(if i.val < 98 then
(if i.val < 97 then
883
else
823)
else
(if i.val < 99 then
858
else
(if i.val < 100 then
243
else
979))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
929
else
208)
else
(if i.val < 104 then
233
else
221))
else
(if i.val < 107 then
(if i.val < 106 then
981
else
271)
else
(if i.val < 108 then
866
else
207)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
864
else
180)
else
(if i.val < 112 then
215
else
255))
else
(if i.val < 115 then
(if i.val < 114 then
963
else
156)
else
(if i.val < 116 then
195
else
(if i.val < 117 then
12
else
964)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
251
else
178)
else
(if i.val < 121 then
265
else
231))
else
(if i.val < 124 then
(if i.val < 123 then
983
else
877)
else
(if i.val < 125 then
817
else
236)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
914
else
276)
else
(if i.val < 129 then
880
else
179))
else
(if i.val < 132 then
(if i.val < 131 then
155
else
919)
else
(if i.val < 133 then
918
else
(if i.val < 134 then
190
else
847))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
257
else
965)
else
(if i.val < 138 then
188
else
318))
else
(if i.val < 141 then
(if i.val < 140 then
379
else
300)
else
(if i.val < 142 then
390
else
363)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
406
else
26)
else
(if i.val < 146 then
334
else
477))
else
(if i.val < 149 then
(if i.val < 148 then
34
else
329)
else
(if i.val < 150 then
996
else
516))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
336
else
321)
else
(if i.val < 154 then
466
else
307))
else
(if i.val < 157 then
(if i.val < 156 then
465
else
461)
else
(if i.val < 158 then
510
else
386)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
410
else
995)
else
(if i.val < 162 then
1050
else
536))
else
(if i.val < 165 then
(if i.val < 164 then
392
else
50)
else
(if i.val < 166 then
373
else
(if i.val < 167 then
399
else
21))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
1040
else
997)
else
(if i.val < 171 then
303
else
365))
else
(if i.val < 174 then
(if i.val < 173 then
296
else
370)
else
(if i.val < 175 then
366
else
498)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
468
else
500)
else
(if i.val < 179 then
433
else
351))
else
(if i.val < 182 then
(if i.val < 181 then
482
else
424)
else
(if i.val < 183 then
347
else
(if i.val < 184 then
311
else
297)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
25
else
428)
else
(if i.val < 188 then
531
else
398))
else
(if i.val < 191 then
(if i.val < 190 then
471
else
441)
else
(if i.val < 192 then
310
else
1043)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
438
else
27)
else
(if i.val < 196 then
408
else
384))
else
(if i.val < 199 then
(if i.val < 198 then
447
else
37)
else
(if i.val < 200 then
401
else
(if i.val < 201 then
39
else
1016)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
421
else
400)
else
(if i.val < 205 then
23
else
422))
else
(if i.val < 208 then
(if i.val < 207 then
30
else
382)
else
(if i.val < 209 then
316
else
312)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
42
else
22)
else
(if i.val < 213 then
317
else
31))
else
(if i.val < 216 then
(if i.val < 215 then
1034
else
507)
else
(if i.val < 217 then
517
else
(if i.val < 218 then
403
else
515)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
33
else
411)
else
(if i.val < 222 then
314
else
327))
else
(if i.val < 225 then
(if i.val < 224 then
356
else
298)
else
(if i.val < 226 then
402
else
35)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
47
else
1005)
else
(if i.val < 230 then
452
else
49))
else
(if i.val < 233 then
(if i.val < 232 then
459
else
1047)
else
(if i.val < 234 then
385
else
(if i.val < 235 then
426
else
451))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
991
else
355)
else
(if i.val < 239 then
535
else
445))
else
(if i.val < 242 then
(if i.val < 241 then
1063
else
469)
else
(if i.val < 243 then
331
else
475)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
46
else
1058)
else
(if i.val < 247 then
509
else
522))
else
(if i.val < 250 then
(if i.val < 249 then
52
else
521)
else
(if i.val < 251 then
354
else
(if i.val < 252 then
435
else
341)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
442
else
530)
else
(if i.val < 256 then
323
else
1015))
else
(if i.val < 259 then
(if i.val < 258 then
440
else
32)
else
(if i.val < 260 then
43
else
389)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
443
else
1037)
else
(if i.val < 264 then
463
else
1064))
else
(if i.val < 267 then
(if i.val < 266 then
41
else
533)
else
(if i.val < 268 then
414
else
(if i.val < 269 then
349
else
504)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
483
else
45)
else
(if i.val < 273 then
1060
else
988))
else
(if i.val < 276 then
(if i.val < 275 then
344
else
1051)
else
(if i.val < 277 then
53
else
330)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
993
else
489)
else
(if i.val < 281 then
448
else
506))
else
(if i.val < 284 then
(if i.val < 283 then
1000
else
340)
else
(if i.val < 285 then
1035
else
1039))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
472
else
405)
else
(if i.val < 289 then
1021
else
348))
else
(if i.val < 292 then
(if i.val < 291 then
481
else
350)
else
(if i.val < 293 then
352
else
28)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
1055
else
648)
else
(if i.val < 297 then
662
else
551))
else
(if i.val < 300 then
(if i.val < 299 then
570
else
537)
else
(if i.val < 301 then
549
else
(if i.val < 302 then
124
else
645))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
542
else
709)
else
(if i.val < 306 then
776
else
636))
else
(if i.val < 309 then
(if i.val < 308 then
598
else
656)
else
(if i.val < 310 then
64
else
743)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
563
else
788)
else
(if i.val < 314 then
613
else
104))
else
(if i.val < 317 then
(if i.val < 316 then
578
else
102)
else
(if i.val < 318 then
547
else
(if i.val < 319 then
594
else
586)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
697
else
91)
else
(if i.val < 323 then
75
else
112))
else
(if i.val < 326 then
(if i.val < 325 then
63
else
559)
else
(if i.val < 327 then
136
else
93)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
98
else
590)
else
(if i.val < 331 then
737
else
561))
else
(if i.val < 334 then
(if i.val < 333 then
100
else
87)
else
(if i.val < 335 then
86
else
(if i.val < 336 then
1066
else
696)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
556
else
608)
else
(if i.val < 340 then
678
else
702))
else
(if i.val < 343 then
(if i.val < 342 then
616
else
690)
else
(if i.val < 344 then
1077
else
718)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
637
else
107)
else
(if i.val < 348 then
632
else
685))
else
(if i.val < 351 then
(if i.val < 350 then
90
else
763)
else
(if i.val < 352 then
129
else
(if i.val < 353 then
686
else
767)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
624
else
692)
else
(if i.val < 357 then
591
else
74))
else
(if i.val < 360 then
(if i.val < 359 then
79
else
65)
else
(if i.val < 361 then
623
else
3)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
579
else
61)
else
(if i.val < 365 then
725
else
60))
else
(if i.val < 368 then
(if i.val < 367 then
664
else
660)
else
(if i.val < 369 then
59
else
(if i.val < 370 then
646
else
70))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
538
else
689)
else
(if i.val < 374 then
628
else
721))
else
(if i.val < 377 then
(if i.val < 376 then
758
else
643)
else
(if i.val < 378 then
89
else
653)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
652
else
605)
else
(if i.val < 382 then
588
else
108))
else
(if i.val < 385 then
(if i.val < 384 then
126
else
641)
else
(if i.val < 386 then
103
else
(if i.val < 387 then
673
else
683)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
552
else
58)
else
(if i.val < 391 then
580
else
109))
else
(if i.val < 394 then
(if i.val < 393 then
699
else
73)
else
(if i.val < 395 then
638
else
610)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
95
else
132)
else
(if i.val < 399 then
137
else
630))
else
(if i.val < 402 then
(if i.val < 401 then
739
else
713)
else
(if i.val < 403 then
584
else
(if i.val < 404 then
78
else
715))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
543
else
736)
else
(if i.val < 408 then
644
else
115))
else
(if i.val < 411 then
(if i.val < 410 then
704
else
72)
else
(if i.val < 412 then
703
else
77)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
712
else
575)
else
(if i.val < 416 then
540
else
566))
else
(if i.val < 419 then
(if i.val < 418 then
117
else
668)
else
(if i.val < 420 then
710
else
101))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
595
else
655)
else
(if i.val < 424 then
57
else
85))
else
(if i.val < 427 then
(if i.val < 426 then
97
else
71)
else
(if i.val < 428 then
69
else
1068)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
733
else
785)
else
(if i.val < 432 then
582
else
123))
else
(if i.val < 435 then
(if i.val < 434 then
119
else
553)
else
(if i.val < 436 then
118
else
(if i.val < 437 then
642
else
618))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
67
else
746)
else
(if i.val < 441 then
135
else
133))
else
(if i.val < 444 then
(if i.val < 443 then
750
else
700)
else
(if i.val < 445 then
728
else
693)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
116
else
4)
else
(if i.val < 449 then
740
else
603))
else
(if i.val < 452 then
(if i.val < 451 then
55
else
639)
else
(if i.val < 453 then
619
else
(if i.val < 454 then
573
else
94)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
787
else
769)
else
(if i.val < 458 then
96
else
680))
else
(if i.val < 461 then
(if i.val < 460 then
121
else
545)
else
(if i.val < 462 then
114
else
778)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
752
else
792)
else
(if i.val < 466 then
130
else
626))
else
(if i.val < 469 then
(if i.val < 468 then
1078
else
627)
else
(if i.val < 470 then
747
else
(if i.val < 471 then
679
else
687)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
775
else
585)
else
(if i.val < 475 then
793
else
99))
else
(if i.val < 478 then
(if i.val < 477 then
777
else
76)
else
(if i.val < 479 then
765
else
1073)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
1065
else
574)
else
(if i.val < 483 then
110
else
734))
else
(if i.val < 486 then
(if i.val < 485 then
759
else
677)
else
(if i.val < 487 then
766
else
(if i.val < 488 then
569
else
611)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
701
else
134)
else
(if i.val < 492 then
756
else
557))
else
(if i.val < 495 then
(if i.val < 494 then
2
else
560)
else
(if i.val < 496 then
581
else
113)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
1076
else
539)
else
(if i.val < 500 then
82
else
674))
else
(if i.val < 503 then
(if i.val < 502 then
92
else
726)
else
(if i.val < 504 then
789
else
(if i.val < 505 then
597
else
1070))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
615
else
111)
else
(if i.val < 509 then
753
else
670))
else
(if i.val < 512 then
(if i.val < 511 then
790
else
576)
else
(if i.val < 513 then
706
else
791)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
761
else
629)
else
(if i.val < 517 then
738
else
742))
else
(if i.val < 520 then
(if i.val < 519 then
650
else
783)
else
(if i.val < 521 then
794
else
(if i.val < 522 then
640
else
622)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
768
else
567)
else
(if i.val < 526 then
708
else
122))
else
(if i.val < 529 then
(if i.val < 528 then
564
else
654)
else
(if i.val < 530 then
131
else
760)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
550
else
781)
else
(if i.val < 534 then
657
else
1067))
else
(if i.val < 537 then
(if i.val < 536 then
711
else
667)
else
(if i.val < 538 then
816
else
(if i.val < 539 then
848
else
175))))))))))
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
11
else
258)
else
(if i.val < 543 then
170
else
287))
else
(if i.val < 546 then
(if i.val < 545 then
144
else
947)
else
(if i.val < 547 then
815
else
212)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
147
else
140)
else
(if i.val < 551 then
187
else
184))
else
(if i.val < 554 then
(if i.val < 553 then
906
else
971)
else
(if i.val < 555 then
808
else
273))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
865
else
950)
else
(if i.val < 559 then
830
else
944))
else
(if i.val < 562 then
(if i.val < 561 then
803
else
242)
else
(if i.val < 563 then
272
else
183)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
936
else
211)
else
(if i.val < 567 then
833
else
955))
else
(if i.val < 570 then
(if i.val < 569 then
167
else
902)
else
(if i.val < 571 then
224
else
(if i.val < 572 then
845
else
855))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
956
else
290)
else
(if i.val < 576 then
267
else
911))
else
(if i.val < 579 then
(if i.val < 578 then
834
else
856)
else
(if i.val < 580 then
5
else
141)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
812
else
896)
else
(if i.val < 584 then
213
else
225))
else
(if i.val < 587 then
(if i.val < 586 then
843
else
861)
else
(if i.val < 588 then
954
else
(if i.val < 589 then
959
else
288)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
148
else
223)
else
(if i.val < 593 then
230
else
160))
else
(if i.val < 596 then
(if i.val < 595 then
138
else
202)
else
(if i.val < 597 then
933
else
269)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
154
else
795)
else
(if i.val < 601 then
264
else
201))
else
(if i.val < 604 then
(if i.val < 603 then
200
else
798)
else
(if i.val < 605 then
882
else
(if i.val < 606 then
939
else
887)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
953
else
982)
else
(if i.val < 610 then
807
else
927))
else
(if i.val < 613 then
(if i.val < 612 then
905
else
232)
else
(if i.val < 614 then
870
else
852)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
281
else
252)
else
(if i.val < 618 then
169
else
13))
else
(if i.val < 621 then
(if i.val < 620 then
229
else
871)
else
(if i.val < 622 then
293
else
(if i.val < 623 then
247
else
934)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
250
else
962)
else
(if i.val < 627 then
153
else
176))
else
(if i.val < 630 then
(if i.val < 629 then
165
else
218)
else
(if i.val < 631 then
166
else
952)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
182
else
17)
else
(if i.val < 635 then
857
else
284))
else
(if i.val < 638 then
(if i.val < 637 then
853
else
802)
else
(if i.val < 639 then
837
else
(if i.val < 640 then
235
else
249))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
196
else
867)
else
(if i.val < 644 then
820
else
15))
else
(if i.val < 647 then
(if i.val < 646 then
888
else
8)
else
(if i.val < 648 then
275
else
925)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
916
else
931)
else
(if i.val < 652 then
14
else
139))
else
(if i.val < 655 then
(if i.val < 654 then
897
else
978)
else
(if i.val < 656 then
205
else
(if i.val < 657 then
949
else
266)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
868
else
204)
else
(if i.val < 661 then
917
else
932))
else
(if i.val < 664 then
(if i.val < 663 then
172
else
185)
else
(if i.val < 665 then
174
else
149)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
922
else
162)
else
(if i.val < 669 then
874
else
915))
else
(if i.val < 672 then
(if i.val < 671 then
246
else
219)
else
(if i.val < 673 then
943
else
(if i.val < 674 then
158
else
177))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
889
else
903)
else
(if i.val < 678 then
851
else
926))
else
(if i.val < 681 then
(if i.val < 680 then
841
else
958)
else
(if i.val < 682 then
886
else
248)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
16
else
825)
else
(if i.val < 686 then
289
else
292))
else
(if i.val < 689 then
(if i.val < 688 then
189
else
294)
else
(if i.val < 690 then
957
else
18))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
831
else
237)
else
(if i.val < 694 then
239
else
227))
else
(if i.val < 697 then
(if i.val < 696 then
862
else
151)
else
(if i.val < 698 then
869
else
214)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
163
else
261)
else
(if i.val < 702 then
279
else
283))
else
(if i.val < 705 then
(if i.val < 704 then
220
else
961)
else
(if i.val < 706 then
192
else
(if i.val < 707 then
821
else
860))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
840
else
937)
else
(if i.val < 711 then
960
else
238))
else
(if i.val < 714 then
(if i.val < 713 then
844
else
199)
else
(if i.val < 715 then
262
else
850)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
835
else
967)
else
(if i.val < 719 then
274
else
901))
else
(if i.val < 722 then
(if i.val < 721 then
805
else
10)
else
(if i.val < 723 then
226
else
(if i.val < 724 then
164
else
890)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
913
else
800)
else
(if i.val < 728 then
863
else
836))
else
(if i.val < 731 then
(if i.val < 730 then
849
else
194)
else
(if i.val < 732 then
824
else
256)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
818
else
270)
else
(if i.val < 736 then
259
else
143))
else
(if i.val < 739 then
(if i.val < 738 then
277
else
150)
else
(if i.val < 740 then
203
else
(if i.val < 741 then
280
else
909)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
216
else
191)
else
(if i.val < 745 then
940
else
240))
else
(if i.val < 748 then
(if i.val < 747 then
828
else
241)
else
(if i.val < 749 then
278
else
923)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
253
else
975)
else
(if i.val < 753 then
263
else
951))
else
(if i.val < 756 then
(if i.val < 755 then
161
else
966)
else
(if i.val < 757 then
924
else
(if i.val < 758 then
285
else
898)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
942
else
254)
else
(if i.val < 762 then
970
else
980))
else
(if i.val < 765 then
(if i.val < 764 then
291
else
938)
else
(if i.val < 766 then
968
else
829)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
977
else
908)
else
(if i.val < 770 then
928
else
801))
else
(if i.val < 773 then
(if i.val < 772 then
945
else
839)
else
(if i.val < 774 then
245
else
(if i.val < 775 then
920
else
286))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
904
else
809)
else
(if i.val < 779 then
973
else
859))
else
(if i.val < 782 then
(if i.val < 781 then
842
else
976)
else
(if i.val < 783 then
168
else
893)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
884
else
819)
else
(if i.val < 787 then
854
else
935))
else
(if i.val < 790 then
(if i.val < 789 then
209
else
974)
else
(if i.val < 791 then
157
else
(if i.val < 792 then
799
else
838)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
912
else
875)
else
(if i.val < 796 then
36
else
396))
else
(if i.val < 799 then
(if i.val < 798 then
987
else
449)
else
(if i.val < 800 then
513
else
502)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
998
else
345)
else
(if i.val < 804 then
494
else
357))
else
(if i.val < 807 then
(if i.val < 806 then
1029
else
309)
else
(if i.val < 808 then
51
else
(if i.val < 809 then
1011
else
476)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
377
else
450)
else
(if i.val < 813 then
495
else
454))
else
(if i.val < 816 then
(if i.val < 815 then
333
else
992)
else
(if i.val < 817 then
299
else
301)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
429
else
430)
else
(if i.val < 821 then
376
else
512))
else
(if i.val < 824 then
(if i.val < 823 then
480
else
425)
else
(if i.val < 825 then
1041
else
985))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
479
else
358)
else
(if i.val < 829 then
439
else
486))
else
(if i.val < 832 then
(if i.val < 831 then
1010
else
994)
else
(if i.val < 833 then
534
else
416)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
1025
else
1057)
else
(if i.val < 837 then
444
else
394))
else
(if i.val < 840 then
(if i.val < 839 then
464
else
990)
else
(if i.val < 841 then
525
else
(if i.val < 842 then
470
else
1008))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
473
else
413)
else
(if i.val < 846 then
1022
else
1056))
else
(if i.val < 849 then
(if i.val < 848 then
490
else
371)
else
(if i.val < 850 then
1023
else
404)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
485
else
999)
else
(if i.val < 854 then
306
else
1012))
else
(if i.val < 857 then
(if i.val < 856 then
1049
else
315)
else
(if i.val < 858 then
0
else
(if i.val < 859 then
328
else
24)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
38
else
319)
else
(if i.val < 863 then
1053
else
1017))
else
(if i.val < 866 then
(if i.val < 865 then
391
else
337)
else
(if i.val < 867 then
346
else
436)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
20
else
320)
else
(if i.val < 871 then
313
else
1044))
else
(if i.val < 874 then
(if i.val < 873 then
493
else
359)
else
(if i.val < 875 then
418
else
(if i.val < 876 then
520
else
324)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
432
else
335)
else
(if i.val < 880 then
343
else
1042))
else
(if i.val < 883 then
(if i.val < 882 then
368
else
1048)
else
(if i.val < 884 then
457
else
986)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
497
else
1020)
else
(if i.val < 888 then
54
else
302))
else
(if i.val < 891 then
(if i.val < 890 then
1014
else
1002)
else
(if i.val < 892 then
412
else
(if i.val < 893 then
322
else
519)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
1001
else
467)
else
(if i.val < 897 then
431
else
378))
else
(if i.val < 900 then
(if i.val < 899 then
375
else
499)
else
(if i.val < 901 then
361
else
1061)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
487
else
989)
else
(if i.val < 905 then
305
else
488))
else
(if i.val < 908 then
(if i.val < 907 then
388
else
427)
else
(if i.val < 909 then
523
else
(if i.val < 910 then
40
else
48))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
511
else
474)
else
(if i.val < 914 then
364
else
383))
else
(if i.val < 917 then
(if i.val < 916 then
1027
else
1018)
else
(if i.val < 918 then
367
else
397)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
529
else
1033)
else
(if i.val < 922 then
1013
else
44))
else
(if i.val < 925 then
(if i.val < 924 then
1004
else
491)
else
(if i.val < 926 then
295
else
(if i.val < 927 then
339
else
395)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
456
else
420)
else
(if i.val < 931 then
29
else
518))
else
(if i.val < 934 then
(if i.val < 933 then
1036
else
984)
else
(if i.val < 935 then
360
else
455)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
527
else
304)
else
(if i.val < 939 then
1019
else
380))
else
(if i.val < 942 then
(if i.val < 941 then
1007
else
1028)
else
(if i.val < 943 then
484
else
(if i.val < 944 then
1006
else
325))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
1026
else
393)
else
(if i.val < 948 then
460
else
1054))
else
(if i.val < 951 then
(if i.val < 950 then
308
else
492)
else
(if i.val < 952 then
508
else
1059)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
19
else
1032)
else
(if i.val < 956 then
524
else
453))
else
(if i.val < 959 then
(if i.val < 958 then
372
else
458)
else
(if i.val < 960 then
381
else
419))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
409
else
1062)
else
(if i.val < 964 then
496
else
417))
else
(if i.val < 967 then
(if i.val < 966 then
326
else
1030)
else
(if i.val < 968 then
1003
else
478)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
1024
else
514)
else
(if i.val < 972 then
434
else
505))
else
(if i.val < 975 then
(if i.val < 974 then
462
else
503)
else
(if i.val < 976 then
1009
else
(if i.val < 977 then
532
else
353))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
528
else
332)
else
(if i.val < 981 then
1038
else
1046))
else
(if i.val < 984 then
(if i.val < 983 then
338
else
526)
else
(if i.val < 985 then
596
else
684)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
784
else
68)
else
(if i.val < 989 then
555
else
676))
else
(if i.val < 992 then
(if i.val < 991 then
772
else
125)
else
(if i.val < 993 then
546
else
(if i.val < 994 then
748
else
691)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
593
else
665)
else
(if i.val < 998 then
617
else
770))
else
(if i.val < 1001 then
(if i.val < 1000 then
614
else
56)
else
(if i.val < 1002 then
1069
else
724)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
717
else
749)
else
(if i.val < 1006 then
62
else
672))
else
(if i.val < 1009 then
(if i.val < 1008 then
744
else
780)
else
(if i.val < 1010 then
751
else
(if i.val < 1011 then
558
else
554)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
786
else
1072)
else
(if i.val < 1015 then
675
else
732))
else
(if i.val < 1018 then
(if i.val < 1017 then
601
else
727)
else
(if i.val < 1019 then
649
else
764)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
681
else
589)
else
(if i.val < 1023 then
571
else
729))
else
(if i.val < 1026 then
(if i.val < 1025 then
1071
else
577)
else
(if i.val < 1027 then
771
else
(if i.val < 1028 then
669
else
66)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
720
else
755)
else
(if i.val < 1032 then
651
else
587))
else
(if i.val < 1035 then
(if i.val < 1034 then
774
else
698)
else
(if i.val < 1036 then
635
else
661)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
714
else
762)
else
(if i.val < 1040 then
757
else
782))
else
(if i.val < 1043 then
(if i.val < 1042 then
731
else
128)
else
(if i.val < 1044 then
705
else
(if i.val < 1045 then
620
else
633))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
105
else
612)
else
(if i.val < 1049 then
604
else
572))
else
(if i.val < 1052 then
(if i.val < 1051 then
754
else
647)
else
(if i.val < 1053 then
80
else
695)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
1074
else
688)
else
(if i.val < 1057 then
88
else
716))
else
(if i.val < 1060 then
(if i.val < 1059 then
773
else
631)
else
(if i.val < 1061 then
562
else
(if i.val < 1062 then
719
else
625)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
745
else
600)
else
(if i.val < 1066 then
822
else
878))
else
(if i.val < 1069 then
(if i.val < 1068 then
832
else
186)
else
(if i.val < 1070 then
894
else
972)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
969
else
921)
else
(if i.val < 1074 then
826
else
948))
else
(if i.val < 1077 then
(if i.val < 1076 then
910
else
885)
else
(if i.val < 1078 then
879
else
(if i.val < 1079 then
895
else
210)))))))))))

def g32p_row06_cosetBranchNextColumn1 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
168
else
23)
else
(if i.val < 3 then
302
else
359))
else
(if i.val < 6 then
(if i.val < 5 then
40
else
68)
else
(if i.val < 7 then
1
else
69)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
70
else
56)
else
(if i.val < 11 then
95
else
551))
else
(if i.val < 14 then
(if i.val < 13 then
73
else
60)
else
(if i.val < 15 then
114
else
90))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
646
else
647)
else
(if i.val < 19 then
614
else
138))
else
(if i.val < 22 then
(if i.val < 21 then
169
else
170)
else
(if i.val < 23 then
5
else
6)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
7
else
8)
else
(if i.val < 27 then
145
else
171))
else
(if i.val < 30 then
(if i.val < 29 then
12
else
172)
else
(if i.val < 31 then
173
else
(if i.val < 32 then
174
else
141))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
142
else
143)
else
(if i.val < 36 then
10
else
225))
else
(if i.val < 39 then
(if i.val < 38 then
146
else
14)
else
(if i.val < 40 then
187
else
163)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
820
else
821)
else
(if i.val < 44 then
288
else
205))
else
(if i.val < 47 then
(if i.val < 46 then
844
else
218)
else
(if i.val < 48 then
235
else
(if i.val < 49 then
880
else
921)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
244
else
799)
else
(if i.val < 53 then
922
else
881))
else
(if i.val < 56 then
(if i.val < 55 then
160
else
19)
else
(if i.val < 57 then
295
else
296)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
297
else
305)
else
(if i.val < 61 then
346
else
34))
else
(if i.val < 64 then
(if i.val < 63 then
360
else
361)
else
(if i.val < 65 then
362
else
(if i.val < 66 then
0
else
20)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
21
else
22)
else
(if i.val < 70 then
24
else
25))
else
(if i.val < 73 then
(if i.val < 72 then
26
else
27)
else
(if i.val < 74 then
28
else
29)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
30
else
31)
else
(if i.val < 78 then
363
else
364))
else
(if i.val < 81 then
(if i.val < 80 then
365
else
356)
else
(if i.val < 82 then
366
else
(if i.val < 83 then
367
else
368)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
369
else
370)
else
(if i.val < 87 then
371
else
54))
else
(if i.val < 90 then
(if i.val < 89 then
32
else
303)
else
(if i.val < 91 then
304
else
39)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
306
else
307)
else
(if i.val < 95 then
308
else
35))
else
(if i.val < 98 then
(if i.val < 97 then
36
else
37)
else
(if i.val < 99 then
321
else
(if i.val < 100 then
454
else
455))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
422
else
339)
else
(if i.val < 104 then
478
else
352))
else
(if i.val < 107 then
(if i.val < 106 then
514
else
1002)
else
(if i.val < 108 then
378
else
433)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
1003
else
515)
else
(if i.val < 112 then
431
else
463))
else
(if i.val < 115 then
(if i.val < 114 then
1053
else
38)
else
(if i.val < 116 then
423
else
(if i.val < 117 then
391
else
1016)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
524
else
477)
else
(if i.val < 121 then
340
else
334))
else
(if i.val < 124 then
(if i.val < 123 then
409
else
1008)
else
(if i.val < 125 then
312
else
344)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
521
else
50)
else
(if i.val < 129 then
473
else
380))
else
(if i.val < 132 then
(if i.val < 131 then
1049
else
513)
else
(if i.val < 133 then
456
else
(if i.val < 134 then
396
else
1000))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
1010
else
516)
else
(if i.val < 138 then
1005
else
55))
else
(if i.val < 141 then
(if i.val < 140 then
57
else
58)
else
(if i.val < 142 then
88
else
537)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
61
else
538)
else
(if i.val < 146 then
71
else
97))
else
(if i.val < 149 then
(if i.val < 148 then
539
else
540)
else
(if i.val < 150 then
541
else
648))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
595
else
104)
else
(if i.val < 154 then
649
else
638))
else
(if i.val < 157 then
(if i.val < 156 then
650
else
651)
else
(if i.val < 158 then
80
else
652)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
653
else
87)
else
(if i.val < 162 then
2
else
3))
else
(if i.val < 165 then
(if i.val < 164 then
4
else
59)
else
(if i.val < 166 then
62
else
(if i.val < 167 then
63
else
64))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
65
else
66)
else
(if i.val < 171 then
67
else
72))
else
(if i.val < 174 then
(if i.val < 173 then
74
else
75)
else
(if i.val < 175 then
76
else
77)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
78
else
79)
else
(if i.val < 179 then
81
else
82))
else
(if i.val < 182 then
(if i.val < 181 then
83
else
84)
else
(if i.val < 183 then
85
else
(if i.val < 184 then
86
else
102)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
632
else
654)
else
(if i.val < 188 then
91
else
655))
else
(if i.val < 191 then
(if i.val < 190 then
639
else
656)
else
(if i.val < 192 then
657
else
658)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
579
else
107)
else
(if i.val < 196 then
659
else
129))
else
(if i.val < 199 then
(if i.val < 198 then
558
else
583)
else
(if i.val < 200 then
606
else
(if i.val < 201 then
547
else
645)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
660
else
661)
else
(if i.val < 205 then
662
else
623))
else
(if i.val < 208 then
(if i.val < 207 then
663
else
664)
else
(if i.val < 209 then
590
else
665)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
116
else
89)
else
(if i.val < 213 then
98
else
552))
else
(if i.val < 216 then
(if i.val < 215 then
553
else
554)
else
(if i.val < 217 then
555
else
(if i.val < 218 then
556
else
557)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
548
else
559)
else
(if i.val < 222 then
560
else
561))
else
(if i.val < 225 then
(if i.val < 224 then
562
else
563)
else
(if i.val < 226 then
96
else
99)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
100
else
101)
else
(if i.val < 230 then
132
else
670))
else
(if i.val < 233 then
(if i.val < 232 then
544
else
706)
else
(if i.val < 234 then
747
else
(if i.val < 235 then
570
else
625))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
748
else
707)
else
(if i.val < 239 then
1068
else
615))
else
(if i.val < 242 then
(if i.val < 241 then
761
else
716)
else
(if i.val < 243 then
669
else
133)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
127
else
601)
else
(if i.val < 247 then
753
else
105))
else
(if i.val < 250 then
(if i.val < 249 then
137
else
713)
else
(if i.val < 251 then
572
else
(if i.val < 252 then
794
else
705)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
588
else
745)
else
(if i.val < 256 then
755
else
708))
else
(if i.val < 259 then
(if i.val < 258 then
750
else
569)
else
(if i.val < 260 then
760
else
678)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
757
else
694)
else
(if i.val < 264 then
756
else
1066))
else
(if i.val < 267 then
(if i.val < 266 then
616
else
577)
else
(if i.val < 268 then
126
else
(if i.val < 269 then
732
else
700)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
743
else
130)
else
(if i.val < 273 then
704
else
607))
else
(if i.val < 276 then
(if i.val < 275 then
775
else
752)
else
(if i.val < 277 then
776
else
613)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
131
else
715)
else
(if i.val < 281 then
740
else
785))
else
(if i.val < 284 then
(if i.val < 283 then
136
else
643)
else
(if i.val < 285 then
675
else
780))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
791
else
758)
else
(if i.val < 289 then
622
else
112))
else
(if i.val < 292 then
(if i.val < 291 then
721
else
92)
else
(if i.val < 293 then
602
else
109)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
113
else
9)
else
(if i.val < 297 then
139
else
140))
else
(if i.val < 300 then
(if i.val < 299 then
144
else
147)
else
(if i.val < 301 then
148
else
(if i.val < 302 then
149
else
161))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
211
else
15)
else
(if i.val < 306 then
164
else
291))
else
(if i.val < 309 then
(if i.val < 308 then
795
else
796)
else
(if i.val < 310 then
797
else
798)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
231
else
800)
else
(if i.val < 314 then
801
else
200))
else
(if i.val < 317 then
(if i.val < 316 then
219
else
802)
else
(if i.val < 318 then
803
else
(if i.val < 319 then
216
else
873)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
923
else
212)
else
(if i.val < 323 then
185
else
924))
else
(if i.val < 326 then
(if i.val < 325 then
861
else
886)
else
(if i.val < 327 then
925
else
837)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
221
else
926)
else
(if i.val < 331 then
815
else
154))
else
(if i.val < 334 then
(if i.val < 333 then
189
else
851)
else
(if i.val < 335 then
825
else
(if i.val < 336 then
918
else
927)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
913
else
928)
else
(if i.val < 340 then
184
else
868))
else
(if i.val < 343 then
(if i.val < 342 then
283
else
840)
else
(if i.val < 344 then
201
else
807)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
11
else
13)
else
(if i.val < 348 then
16
else
17))
else
(if i.val < 351 then
(if i.val < 350 then
18
else
150)
else
(if i.val < 352 then
151
else
(if i.val < 353 then
152
else
153)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
155
else
156)
else
(if i.val < 357 then
157
else
158))
else
(if i.val < 360 then
(if i.val < 359 then
159
else
162)
else
(if i.val < 361 then
165
else
166)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
167
else
175)
else
(if i.val < 365 then
176
else
177))
else
(if i.val < 368 then
(if i.val < 367 then
178
else
179)
else
(if i.val < 369 then
180
else
(if i.val < 370 then
181
else
182))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
183
else
186)
else
(if i.val < 374 then
188
else
190))
else
(if i.val < 377 then
(if i.val < 376 then
191
else
192)
else
(if i.val < 378 then
193
else
194)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
195
else
196)
else
(if i.val < 382 then
197
else
198))
else
(if i.val < 385 then
(if i.val < 384 then
199
else
202)
else
(if i.val < 386 then
203
else
(if i.val < 387 then
204
else
206)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
207
else
208)
else
(if i.val < 391 then
209
else
210))
else
(if i.val < 394 then
(if i.val < 393 then
253
else
864)
else
(if i.val < 395 then
915
else
917)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
243
else
867)
else
(if i.val < 399 then
929
else
857))
else
(if i.val < 402 then
(if i.val < 401 then
835
else
814)
else
(if i.val < 403 then
242
else
(if i.val < 404 then
230
else
911))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
266
else
891)
else
(if i.val < 408 then
852
else
930))
else
(if i.val < 411 then
(if i.val < 410 then
907
else
866)
else
(if i.val < 412 then
284
else
816)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
931
else
887)
else
(if i.val < 416 then
260
else
819))
else
(if i.val < 419 then
(if i.val < 418 then
888
else
932)
else
(if i.val < 420 then
933
else
934))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
899
else
228)
else
(if i.val < 424 then
804
else
892))
else
(if i.val < 427 then
(if i.val < 426 then
213
else
848)
else
(if i.val < 428 then
223
else
805)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
214
else
215)
else
(if i.val < 432 then
822
else
269))
else
(if i.val < 435 then
(if i.val < 434 then
823
else
812)
else
(if i.val < 436 then
824
else
(if i.val < 437 then
826
else
827))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
806
else
828)
else
(if i.val < 441 then
829
else
813))
else
(if i.val < 444 then
(if i.val < 443 then
830
else
831)
else
(if i.val < 445 then
832
else
833)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
232
else
257)
else
(if i.val < 449 then
280
else
834))
else
(if i.val < 452 then
(if i.val < 451 then
836
else
838)
else
(if i.val < 453 then
264
else
(if i.val < 454 then
839
else
226)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
227
else
229)
else
(if i.val < 458 then
222
else
233))
else
(if i.val < 461 then
(if i.val < 460 then
234
else
236)
else
(if i.val < 462 then
237
else
972)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
289
else
935)
else
(if i.val < 466 then
890
else
843))
else
(if i.val < 469 then
(if i.val < 468 then
275
else
246)
else
(if i.val < 470 then
968
else
(if i.val < 471 then
879
else
262)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
919
else
882)
else
(if i.val < 475 then
970
else
290))
else
(if i.val < 478 then
(if i.val < 477 then
251
else
906)
else
(if i.val < 479 then
874
else
878)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
281
else
949)
else
(if i.val < 483 then
950
else
287))
else
(if i.val < 486 then
(if i.val < 485 then
889
else
914)
else
(if i.val < 487 then
959
else
(if i.val < 488 then
817
else
849)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
954
else
965)
else
(if i.val < 492 then
895
else
276))
else
(if i.val < 495 then
(if i.val < 494 then
841
else
292)
else
(if i.val < 496 then
940
else
948)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
938
else
856)
else
(if i.val < 500 then
939
else
897))
else
(if i.val < 503 then
(if i.val < 502 then
847
else
258)
else
(if i.val < 504 then
974
else
(if i.val < 505 then
976
else
871))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
808
else
239)
else
(if i.val < 509 then
217
else
865))
else
(if i.val < 512 then
(if i.val < 511 then
961
else
870)
else
(if i.val < 513 then
946
else
278)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
247
else
904)
else
(if i.val < 517 then
282
else
845))
else
(if i.val < 520 then
(if i.val < 519 then
855
else
893)
else
(if i.val < 521 then
955
else
(if i.val < 522 then
267
else
254)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
261
else
905)
else
(if i.val < 526 then
943
else
859))
else
(if i.val < 529 then
(if i.val < 528 then
978
else
894)
else
(if i.val < 530 then
947
else
912)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
858
else
285)
else
(if i.val < 534 then
854
else
273))
else
(if i.val < 537 then
(if i.val < 536 then
936
else
876)
else
(if i.val < 538 then
33
else
(if i.val < 539 then
298
else
299))))))))))
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
300
else
301)
else
(if i.val < 543 then
309
else
310))
else
(if i.val < 546 then
(if i.val < 545 then
311
else
51)
else
(if i.val < 547 then
313
else
314)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
315
else
316)
else
(if i.val < 551 then
317
else
345))
else
(if i.val < 554 then
(if i.val < 553 then
425
else
429)
else
(if i.val < 555 then
430
else
318))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
508
else
46)
else
(if i.val < 559 then
381
else
984))
else
(if i.val < 562 then
(if i.val < 561 then
328
else
457)
else
(if i.val < 563 then
427
else
985)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
428
else
438)
else
(if i.val < 567 then
506
else
986))
else
(if i.val < 570 then
(if i.val < 569 then
987
else
502)
else
(if i.val < 571 then
459
else
(if i.val < 572 then
988
else
989))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
434
else
441)
else
(if i.val < 576 then
401
else
330))
else
(if i.val < 579 then
(if i.val < 578 then
405
else
412)
else
(if i.val < 580 then
377
else
487)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
990
else
416)
else
(if i.val < 584 then
382
else
327))
else
(if i.val < 587 then
(if i.val < 586 then
1018
else
1040)
else
(if i.val < 588 then
404
else
(if i.val < 589 then
392
else
530)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
389
else
526)
else
(if i.val < 593 then
337
else
485))
else
(if i.val < 596 then
(if i.val < 595 then
444
else
351)
else
(if i.val < 597 then
484
else
994)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
1027
else
394)
else
(if i.val < 601 then
397
else
1050))
else
(if i.val < 604 then
(if i.val < 603 then
494
else
533)
else
(if i.val < 605 then
1009
else
(if i.val < 606 then
395
else
383)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
534
else
335)
else
(if i.val < 610 then
472
else
421))
else
(if i.val < 613 then
(if i.val < 612 then
1041
else
393)
else
(if i.val < 614 then
1032
else
349)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
507
else
1028)
else
(if i.val < 618 then
41
else
500))
else
(if i.val < 621 then
(if i.val < 620 then
436
else
1004)
else
(if i.val < 622 then
42
else
(if i.val < 623 then
43
else
44)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
45
else
47)
else
(if i.val < 627 then
48
else
49))
else
(if i.val < 630 then
(if i.val < 629 then
52
else
53)
else
(if i.val < 631 then
319
else
320)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
322
else
323)
else
(if i.val < 635 then
324
else
325))
else
(if i.val < 638 then
(if i.val < 637 then
326
else
329)
else
(if i.val < 639 then
331
else
(if i.val < 640 then
332
else
333))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
336
else
338)
else
(if i.val < 644 then
341
else
342))
else
(if i.val < 647 then
(if i.val < 646 then
343
else
347)
else
(if i.val < 648 then
348
else
350)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
353
else
354)
else
(if i.val < 652 then
355
else
357))
else
(if i.val < 655 then
(if i.val < 654 then
358
else
372)
else
(if i.val < 656 then
373
else
(if i.val < 657 then
374
else
375)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
376
else
379)
else
(if i.val < 661 then
384
else
385))
else
(if i.val < 664 then
(if i.val < 663 then
386
else
387)
else
(if i.val < 665 then
388
else
390)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
398
else
399)
else
(if i.val < 669 then
400
else
402))
else
(if i.val < 672 then
(if i.val < 671 then
403
else
406)
else
(if i.val < 673 then
407
else
(if i.val < 674 then
408
else
410))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
411
else
413)
else
(if i.val < 678 then
414
else
415))
else
(if i.val < 681 then
(if i.val < 680 then
417
else
418)
else
(if i.val < 682 then
419
else
420)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
424
else
426)
else
(if i.val < 686 then
491
else
531))
else
(if i.val < 689 then
(if i.val < 688 then
464
else
1054)
else
(if i.val < 690 then
535
else
1015))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
1039
else
1031)
else
(if i.val < 694 then
1011
else
471))
else
(if i.val < 697 then
(if i.val < 696 then
497
else
499)
else
(if i.val < 698 then
505
else
495)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
440
else
432)
else
(if i.val < 702 then
511
else
1043))
else
(if i.val < 705 then
(if i.val < 704 then
1020
else
1052)
else
(if i.val < 706 then
997
else
(if i.val < 707 then
446
else
461))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
999
else
525)
else
(if i.val < 711 then
1014
else
1029))
else
(if i.val < 714 then
(if i.val < 713 then
465
else
995)
else
(if i.val < 715 then
451
else
992)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
1036
else
512)
else
(if i.val < 719 then
529
else
496))
else
(if i.val < 722 then
(if i.val < 721 then
528
else
475)
else
(if i.val < 723 then
481
else
(if i.val < 724 then
482
else
518)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
1013
else
996)
else
(if i.val < 728 then
1044
else
1022))
else
(if i.val < 731 then
(if i.val < 730 then
435
else
437)
else
(if i.val < 732 then
520
else
1006)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
1007
else
449)
else
(if i.val < 736 then
474
else
498))
else
(if i.val < 739 then
(if i.val < 738 then
998
else
501)
else
(if i.val < 740 then
469
else
(if i.val < 741 then
448
else
486)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
450
else
1012)
else
(if i.val < 745 then
453
else
522))
else
(if i.val < 748 then
(if i.val < 747 then
439
else
458)
else
(if i.val < 749 then
460
else
462)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
447
else
466)
else
(if i.val < 753 then
467
else
468))
else
(if i.val < 756 then
(if i.val < 755 then
470
else
1051)
else
(if i.val < 757 then
1030
else
(if i.val < 758 then
523
else
483)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
1035
else
1046)
else
(if i.val < 762 then
1021
else
1019))
else
(if i.val < 765 then
(if i.val < 764 then
490
else
1055)
else
(if i.val < 766 then
1057
else
442)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
1042
else
504)
else
(if i.val < 770 then
479
else
489))
else
(if i.val < 773 then
(if i.val < 772 then
527
else
1024)
else
(if i.val < 774 then
493
else
(if i.val < 775 then
1059
else
993))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
492
else
488)
else
(if i.val < 779 then
1017
else
510))
else
(if i.val < 782 then
(if i.val < 781 then
532
else
443)
else
(if i.val < 783 then
536
else
519)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1023
else
480)
else
(if i.val < 787 then
1025
else
1037))
else
(if i.val < 790 then
(if i.val < 789 then
1056
else
503)
else
(if i.val < 791 then
1060
else
(if i.val < 792 then
991
else
1062)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
1063
else
476)
else
(if i.val < 796 then
93
else
94))
else
(if i.val < 799 then
(if i.val < 798 then
542
else
543)
else
(if i.val < 800 then
545
else
124)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
546
else
549)
else
(if i.val < 804 then
550
else
115))
else
(if i.val < 807 then
(if i.val < 806 then
564
else
565)
else
(if i.val < 808 then
125
else
(if i.val < 809 then
566
else
567)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
568
else
571)
else
(if i.val < 813 then
573
else
574))
else
(if i.val < 816 then
(if i.val < 815 then
575
else
576)
else
(if i.val < 817 then
578
else
580)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
581
else
582)
else
(if i.val < 821 then
617
else
621))
else
(if i.val < 824 then
(if i.val < 823 then
111
else
108)
else
(if i.val < 825 then
729
else
121))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
619
else
730)
else
(if i.val < 829 then
746
else
699))
else
(if i.val < 832 then
(if i.val < 831 then
766
else
781)
else
(if i.val < 833 then
594
else
1065)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
734
else
668)
else
(if i.val < 837 then
742
else
584))
else
(if i.val < 840 then
(if i.val < 839 then
714
else
744)
else
(if i.val < 841 then
644
else
(if i.val < 842 then
773
else
597))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
751
else
624)
else
(if i.val < 846 then
1067
else
726))
else
(if i.val < 849 then
(if i.val < 848 then
738
else
684)
else
(if i.val < 850 then
777
else
737)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
640
else
672)
else
(if i.val < 854 then
134
else
603))
else
(if i.val < 857 then
(if i.val < 856 then
724
else
736)
else
(if i.val < 858 then
667
else
(if i.val < 859 then
686
else
591)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
692
else
634)
else
(if i.val < 863 then
1074
else
1070))
else
(if i.val < 866 then
(if i.val < 865 then
612
else
1072)
else
(if i.val < 867 then
674
else
600)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
120
else
778)
else
(if i.val < 871 then
701
else
697))
else
(if i.val < 874 then
(if i.val < 873 then
117
else
630)
else
(if i.val < 875 then
103
else
(if i.val < 876 then
784
else
782)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
691
else
769)
else
(if i.val < 880 then
754
else
626))
else
(if i.val < 883 then
(if i.val < 882 then
629
else
128)
else
(if i.val < 884 then
598
else
611)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
688
else
635)
else
(if i.val < 888 then
677
else
679))
else
(if i.val < 891 then
(if i.val < 890 then
596
else
712)
else
(if i.val < 892 then
671
else
(if i.val < 893 then
683
else
783)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
720
else
685)
else
(if i.val < 897 then
693
else
618))
else
(if i.val < 900 then
(if i.val < 899 then
786
else
610)
else
(if i.val < 901 then
586
else
764)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
788
else
106)
else
(if i.val < 905 then
110
else
118))
else
(if i.val < 908 then
(if i.val < 907 then
119
else
122)
else
(if i.val < 909 then
123
else
(if i.val < 910 then
135
else
585))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
587
else
589)
else
(if i.val < 914 then
592
else
593))
else
(if i.val < 917 then
(if i.val < 916 then
599
else
604)
else
(if i.val < 918 then
605
else
608)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
609
else
620)
else
(if i.val < 922 then
627
else
628))
else
(if i.val < 925 then
(if i.val < 924 then
631
else
633)
else
(if i.val < 926 then
636
else
(if i.val < 927 then
637
else
641)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
642
else
666)
else
(if i.val < 931 then
673
else
676))
else
(if i.val < 934 then
(if i.val < 933 then
680
else
681)
else
(if i.val < 935 then
682
else
687)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
689
else
690)
else
(if i.val < 939 then
695
else
696))
else
(if i.val < 942 then
(if i.val < 941 then
698
else
702)
else
(if i.val < 943 then
703
else
(if i.val < 944 then
709
else
710))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
711
else
717)
else
(if i.val < 948 then
718
else
719))
else
(if i.val < 951 then
(if i.val < 950 then
722
else
723)
else
(if i.val < 952 then
725
else
727)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
728
else
770)
else
(if i.val < 956 then
731
else
1071))
else
(if i.val < 959 then
(if i.val < 958 then
1069
else
765)
else
(if i.val < 960 then
741
else
759))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
779
else
787)
else
(if i.val < 964 then
762
else
1077))
else
(if i.val < 967 then
(if i.val < 966 then
763
else
1078)
else
(if i.val < 968 then
1079
else
739)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
733
else
735)
else
(if i.val < 972 then
772
else
749))
else
(if i.val < 975 then
(if i.val < 974 then
774
else
789)
else
(if i.val < 976 then
767
else
(if i.val < 977 then
768
else
1075))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
771
else
792)
else
(if i.val < 981 then
1076
else
793))
else
(if i.val < 984 then
(if i.val < 983 then
1073
else
790)
else
(if i.val < 985 then
220
else
224)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
809
else
810)
else
(if i.val < 989 then
811
else
250))
else
(if i.val < 992 then
(if i.val < 991 then
818
else
286)
else
(if i.val < 993 then
279
else
(if i.val < 994 then
274
else
842)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
249
else
846)
else
(if i.val < 998 then
252
else
850))
else
(if i.val < 1001 then
(if i.val < 1000 then
256
else
853)
else
(if i.val < 1002 then
238
else
903)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
293
else
920)
else
(if i.val < 1006 then
248
else
268))
else
(if i.val < 1009 then
(if i.val < 1008 then
969
else
908)
else
(if i.val < 1010 then
916
else
(if i.val < 1011 then
909
else
896)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
270
else
951)
else
(if i.val < 1015 then
944
else
937))
else
(if i.val < 1018 then
(if i.val < 1017 then
872
else
869)
else
(if i.val < 1019 then
910
else
963)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
942
else
240)
else
(if i.val < 1023 then
953
else
875))
else
(if i.val < 1026 then
(if i.val < 1025 then
971
else
898)
else
(if i.val < 1027 then
957
else
(if i.val < 1028 then
883
else
265)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
945
else
263)
else
(if i.val < 1032 then
860
else
277))
else
(if i.val < 1035 then
(if i.val < 1034 then
863
else
956)
else
(if i.val < 1036 then
960
else
241)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
962
else
862)
else
(if i.val < 1040 then
877
else
900))
else
(if i.val < 1043 then
(if i.val < 1042 then
884
else
975)
else
(if i.val < 1044 then
941
else
(if i.val < 1045 then
952
else
966))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
259
else
967)
else
(if i.val < 1049 then
977
else
271))
else
(if i.val < 1052 then
(if i.val < 1051 then
245
else
255)
else
(if i.val < 1053 then
272
else
294)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
885
else
901)
else
(if i.val < 1057 then
902
else
958))
else
(if i.val < 1060 then
(if i.val < 1059 then
964
else
973)
else
(if i.val < 1061 then
983
else
(if i.val < 1062 then
980
else
979)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
981
else
982)
else
(if i.val < 1066 then
445
else
452))
else
(if i.val < 1069 then
(if i.val < 1068 then
517
else
1001)
else
(if i.val < 1070 then
1026
else
1033)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
1034
else
509)
else
(if i.val < 1074 then
1064
else
1038))
else
(if i.val < 1077 then
(if i.val < 1076 then
1048
else
1061)
else
(if i.val < 1078 then
1058
else
(if i.val < 1079 then
1045
else
1047)))))))))))

def g32p_row06_cosetBranchNextColumn2 : Fin 1080 → Fin 1080 :=
  fun i => (if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
444
else
566)
else
(if i.val < 3 then
546
else
779))
else
(if i.val < 6 then
(if i.val < 5 then
96
else
942)
else
(if i.val < 7 then
6
else
159)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
148
else
154)
else
(if i.val < 11 then
223
else
907))
else
(if i.val < 14 then
(if i.val < 13 then
285
else
983)
else
(if i.val < 15 then
280
else
227))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
171
else
962)
else
(if i.val < 19 then
239
else
452))
else
(if i.val < 22 then
(if i.val < 21 then
423
else
380)
else
(if i.val < 23 then
421
else
491)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
334
else
422)
else
(if i.val < 27 then
347
else
1063))
else
(if i.val < 30 then
(if i.val < 29 then
449
else
310)
else
(if i.val < 31 then
985
else
(if i.val < 32 then
1022
else
1028))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
451
else
416)
else
(if i.val < 36 then
1010
else
1052))
else
(if i.val < 39 then
(if i.val < 38 then
1054
else
448)
else
(if i.val < 40 then
534
else
473)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
443
else
467)
else
(if i.val < 44 then
500
else
356))
else
(if i.val < 47 then
(if i.val < 46 then
1062
else
54)
else
(if i.val < 48 then
47
else
(if i.val < 49 then
474
else
456)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
513
else
367)
else
(if i.val < 53 then
424
else
429))
else
(if i.val < 56 then
(if i.val < 55 then
46
else
102)
else
(if i.val < 57 then
649
else
61)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
695
else
126)
else
(if i.val < 61 then
92
else
57))
else
(if i.val < 64 then
(if i.val < 63 then
715
else
632)
else
(if i.val < 65 then
629
else
(if i.val < 66 then
84
else
756)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
668
else
747)
else
(if i.val < 70 then
602
else
642))
else
(if i.val < 73 then
(if i.val < 72 then
793
else
607)
else
(if i.val < 74 then
130
else
712)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
560
else
663)
else
(if i.val < 78 then
109
else
99))
else
(if i.val < 81 then
(if i.val < 80 then
1076
else
619)
else
(if i.val < 82 then
729
else
(if i.val < 83 then
573
else
125)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
65
else
108)
else
(if i.val < 87 then
576
else
557))
else
(if i.val < 90 then
(if i.val < 89 then
687
else
723)
else
(if i.val < 91 then
705
else
646)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
60
else
745)
else
(if i.val < 95 then
571
else
648))
else
(if i.val < 98 then
(if i.val < 97 then
4
else
727)
else
(if i.val < 99 then
790
else
(if i.val < 100 then
78
else
717))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
760
else
55)
else
(if i.val < 104 then
713
else
697))
else
(if i.val < 107 then
(if i.val < 106 then
117
else
768)
else
(if i.val < 108 then
113
else
85)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
77
else
744)
else
(if i.val < 112 then
652
else
786))
else
(if i.val < 115 then
(if i.val < 114 then
107
else
740)
else
(if i.val < 116 then
639
else
(if i.val < 117 then
714
else
105)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
1073
else
591)
else
(if i.val < 121 then
708
else
750))
else
(if i.val < 124 then
(if i.val < 123 then
608
else
694)
else
(if i.val < 125 then
625
else
83)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
59
else
553)
else
(if i.val < 129 then
763
else
791))
else
(if i.val < 132 then
(if i.val < 131 then
73
else
776)
else
(if i.val < 133 then
784
else
(if i.val < 134 then
1074
else
574))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
773
else
653)
else
(if i.val < 138 then
699
else
922))
else
(if i.val < 141 then
(if i.val < 140 then
864
else
920)
else
(if i.val < 142 then
141
else
868)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
924
else
291)
else
(if i.val < 146 then
273
else
186))
else
(if i.val < 149 then
(if i.val < 148 then
191
else
8)
else
(if i.val < 150 then
946
else
841))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
914
else
894)
else
(if i.val < 154 then
859
else
9))
else
(if i.val < 157 then
(if i.val < 156 then
854
else
893)
else
(if i.val < 158 then
208
else
158)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
7
else
218)
else
(if i.val < 162 then
865
else
253))
else
(if i.val < 165 then
(if i.val < 164 then
198
else
267)
else
(if i.val < 166 then
217
else
(if i.val < 167 then
912
else
244))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
247
else
833)
else
(if i.val < 171 then
944
else
16))
else
(if i.val < 174 then
(if i.val < 173 then
261
else
897)
else
(if i.val < 175 then
254
else
840)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
964
else
871)
else
(if i.val < 179 then
870
else
810))
else
(if i.val < 182 then
(if i.val < 181 then
839
else
290)
else
(if i.val < 183 then
880
else
(if i.val < 184 then
913
else
892)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
796
else
146)
else
(if i.val < 188 then
981
else
948))
else
(if i.val < 191 then
(if i.val < 190 then
263
else
849)
else
(if i.val < 192 then
147
else
235)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
968
else
973)
else
(if i.val < 196 then
842
else
971))
else
(if i.val < 199 then
(if i.val < 198 then
826
else
163)
else
(if i.val < 200 then
874
else
(if i.val < 201 then
815
else
853)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
919
else
969)
else
(if i.val < 205 then
258
else
925))
else
(if i.val < 208 then
(if i.val < 207 then
916
else
945)
else
(if i.val < 209 then
157
else
804)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
902
else
904)
else
(if i.val < 213 then
959
else
850))
else
(if i.val < 216 then
(if i.val < 215 then
276
else
283)
else
(if i.val < 217 then
242
else
(if i.val < 218 then
165
else
160)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
268
else
818)
else
(if i.val < 222 then
288
else
951))
else
(if i.val < 225 then
(if i.val < 224 then
10
else
836)
else
(if i.val < 226 then
965
else
955)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
15
else
845)
else
(if i.val < 230 then
277
else
915))
else
(if i.val < 233 then
(if i.val < 232 then
980
else
232)
else
(if i.val < 234 then
947
else
(if i.val < 235 then
246
else
192))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
939
else
974)
else
(if i.val < 239 then
867
else
18))
else
(if i.val < 242 then
(if i.val < 241 then
264
else
851)
else
(if i.val < 243 then
216
else
863)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
167
else
901)
else
(if i.val < 247 then
234
else
168))
else
(if i.val < 250 then
(if i.val < 249 then
847
else
886)
else
(if i.val < 251 then
289
else
(if i.val < 252 then
827
else
856)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
162
else
174)
else
(if i.val < 256 then
822
else
838))
else
(if i.val < 259 then
(if i.val < 258 then
292
else
204)
else
(if i.val < 260 then
928
else
905)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
172
else
266)
else
(if i.val < 264 then
189
else
240))
else
(if i.val < 267 then
(if i.val < 266 then
935
else
262)
else
(if i.val < 268 then
164
else
(if i.val < 269 then
219
else
967)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
979
else
937)
else
(if i.val < 273 then
882
else
145))
else
(if i.val < 276 then
(if i.val < 275 then
933
else
816)
else
(if i.val < 277 then
214
else
229)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
881
else
982)
else
(if i.val < 281 then
14
else
798))
else
(if i.val < 284 then
(if i.val < 283 then
825
else
215)
else
(if i.val < 285 then
799
else
12))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
835
else
903)
else
(if i.val < 289 then
221
else
250))
else
(if i.val < 292 then
(if i.val < 291 then
181
else
144)
else
(if i.val < 293 then
257
else
293)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
848
else
477)
else
(if i.val < 297 then
525
else
527))
else
(if i.val < 300 then
(if i.val < 299 then
1060
else
413)
else
(if i.val < 301 then
1046
else
(if i.val < 302 then
304
else
488))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
368
else
301)
else
(if i.val < 306 then
521
else
321))
else
(if i.val < 309 then
(if i.val < 308 then
387
else
530)
else
(if i.val < 310 then
984
else
29)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
505
else
376)
else
(if i.val < 314 then
374
else
337))
else
(if i.val < 317 then
(if i.val < 316 then
315
else
1032)
else
(if i.val < 318 then
1053
else
(if i.val < 319 then
433
else
1055)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
1050
else
306)
else
(if i.val < 323 then
470
else
393))
else
(if i.val < 326 then
(if i.val < 325 then
350
else
383)
else
(if i.val < 327 then
436
else
462)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
450
else
1001)
else
(if i.val < 331 then
410
else
526))
else
(if i.val < 334 then
(if i.val < 333 then
445
else
484)
else
(if i.val < 335 then
24
else
(if i.val < 336 then
501
else
993)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
314
else
517)
else
(if i.val < 340 then
1021
else
391))
else
(if i.val < 343 then
(if i.val < 342 then
386
else
1003)
else
(if i.val < 344 then
510
else
515)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
440
else
486)
else
(if i.val < 348 then
26
else
502))
else
(if i.val < 351 then
(if i.val < 350 then
408
else
324)
else
(if i.val < 352 then
414
else
(if i.val < 353 then
1061
else
442)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
354
else
503)
else
(if i.val < 357 then
44
else
1051))
else
(if i.val < 360 then
(if i.val < 359 then
447
else
1000)
else
(if i.val < 361 then
524
else
988)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
492
else
363)
else
(if i.val < 365 then
1040
else
528))
else
(if i.val < 368 then
(if i.val < 367 then
1013
else
51)
else
(if i.val < 369 then
303
else
(if i.val < 370 then
1016
else
402))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
1041
else
1018)
else
(if i.val < 374 then
1017
else
313))
else
(if i.val < 377 then
(if i.val < 376 then
1047
else
312)
else
(if i.val < 378 then
1035
else
535)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
1025
else
21)
else
(if i.val < 382 then
389
else
490))
else
(if i.val < 385 then
(if i.val < 384 then
325
else
1034)
else
(if i.val < 386 then
438
else
(if i.val < 387 then
341
else
307)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
1019
else
381)
else
(if i.val < 391 then
1030
else
340))
else
(if i.val < 394 then
(if i.val < 393 then
441
else
323)
else
(if i.val < 395 then
986
else
995)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
428
else
496)
else
(if i.val < 399 then
1023
else
509))
else
(if i.val < 402 then
(if i.val < 401 then
1024
else
478)
else
(if i.val < 403 then
370
else
(if i.val < 404 then
425
else
454))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
487
else
1049)
else
(if i.val < 408 then
432
else
349))
else
(if i.val < 411 then
(if i.val < 410 then
1005
else
330)
else
(if i.val < 412 then
434
else
507)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
299
else
351)
else
(if i.val < 416 then
992
else
34))
else
(if i.val < 419 then
(if i.val < 418 then
1033
else
460)
else
(if i.val < 420 then
1007
else
1004))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
22
else
25)
else
(if i.val < 424 then
20
else
52))
else
(if i.val < 427 then
(if i.val < 426 then
403
else
1059)
else
(if i.val < 428 then
493
else
396)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
53
else
1037)
else
(if i.val < 432 then
431
else
407))
else
(if i.val < 435 then
(if i.val < 434 then
318
else
411)
else
(if i.val < 436 then
457
else
(if i.val < 437 then
326
else
489))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
385
else
461)
else
(if i.val < 441 then
345
else
392))
else
(if i.val < 444 then
(if i.val < 443 then
353
else
41)
else
(if i.val < 445 then
0
else
332)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
1006
else
358)
else
(if i.val < 449 then
38
else
28))
else
(if i.val < 452 then
(if i.val < 451 then
328
else
33)
else
(if i.val < 453 then
19
else
(if i.val < 454 then
482
else
404)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
498
else
49)
else
(if i.val < 458 then
435
else
495))
else
(if i.val < 461 then
(if i.val < 460 then
476
else
418)
else
(if i.val < 462 then
439
else
327)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
994
else
464)
else
(if i.val < 466 then
480
else
511))
else
(if i.val < 469 then
(if i.val < 468 then
42
else
531)
else
(if i.val < 470 then
472
else
(if i.val < 471 then
322
else
518)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
469
else
40)
else
(if i.val < 475 then
48
else
514))
else
(if i.val < 478 then
(if i.val < 477 then
459
else
295)
else
(if i.val < 479 then
401
else
497)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
465
else
1026)
else
(if i.val < 483 then
453
else
504))
else
(if i.val < 486 then
(if i.val < 485 then
333
else
1036)
else
(if i.val < 487 then
346
else
(if i.val < 488 then
405
else
302)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
437
else
382)
else
(if i.val < 492 then
23
else
362))
else
(if i.val < 495 then
(if i.val < 494 then
427
else
516)
else
(if i.val < 496 then
458
else
397)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
479
else
455)
else
(if i.val < 500 then
990
else
43))
else
(if i.val < 503 then
(if i.val < 502 then
335
else
348)
else
(if i.val < 504 then
355
else
(if i.val < 505 then
483
else
311))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
506
else
412)
else
(if i.val < 509 then
1064
else
399))
else
(if i.val < 512 then
(if i.val < 511 then
343
else
466)
else
(if i.val < 513 then
997
else
50)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
475
else
344)
else
(if i.val < 517 then
494
else
338))
else
(if i.val < 520 then
(if i.val < 519 then
471
else
1031)
else
(if i.val < 521 then
1058
else
(if i.val < 522 then
305
else
1009)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
1045
else
360)
else
(if i.val < 526 then
296
else
331))
else
(if i.val < 529 then
(if i.val < 528 then
297
else
365)
else
(if i.val < 530 then
1020
else
308)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
468
else
1015)
else
(if i.val < 534 then
1039
else
39))
else
(if i.val < 537 then
(if i.val < 536 then
378
else
1038)
else
(if i.val < 538 then
788
else
(if i.val < 539 then
741
else
700))))))))))
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
1067
else
736)
else
(if i.val < 543 then
696
else
1078))
else
(if i.val < 546 then
(if i.val < 545 then
720
else
765)
else
(if i.val < 547 then
2
else
611)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
706
else
627)
else
(if i.val < 551 then
774
else
738))
else
(if i.val < 554 then
(if i.val < 553 then
567
else
127)
else
(if i.val < 555 then
569
else
626))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
678
else
87)
else
(if i.val < 559 then
623
else
748))
else
(if i.val < 562 then
(if i.val < 561 then
75
else
701)
else
(if i.val < 563 then
634
else
622)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
679
else
681)
else
(if i.val < 567 then
1
else
552))
else
(if i.val < 570 then
(if i.val < 569 then
675
else
554)
else
(if i.val < 571 then
770
else
(if i.val < 572 then
94
else
659))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
82
else
134)
else
(if i.val < 576 then
635
else
86))
else
(if i.val < 579 then
(if i.val < 578 then
702
else
673)
else
(if i.val < 580 then
660
else
724)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
680
else
612)
else
(if i.val < 584 then
704
else
711))
else
(if i.val < 587 then
(if i.val < 586 then
688
else
731)
else
(if i.val < 588 then
1077
else
(if i.val < 589 then
645
else
754)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
636
else
119)
else
(if i.val < 593 then
674
else
596))
else
(if i.val < 596 then
(if i.val < 595 then
721
else
640)
else
(if i.val < 597 then
593
else
693)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
654
else
737)
else
(if i.val < 601 then
778
else
1069))
else
(if i.val < 604 then
(if i.val < 603 then
69
else
603)
else
(if i.val < 605 then
728
else
(if i.val < 606 then
606
else
605)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
72
else
122)
else
(if i.val < 610 then
759
else
718))
else
(if i.val < 613 then
(if i.val < 612 then
547
else
582)
else
(if i.val < 614 then
666
else
752)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
621
else
616)
else
(if i.val < 618 then
743
else
742))
else
(if i.val < 621 then
(if i.val < 620 then
80
else
769)
else
(if i.val < 622 then
615
else
(if i.val < 623 then
563
else
558)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
726
else
124)
else
(if i.val < 627 then
555
else
549))
else
(if i.val < 630 then
(if i.val < 629 then
761
else
64)
else
(if i.val < 631 then
631
else
630)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
63
else
709)
else
(if i.val < 635 then
562
else
575))
else
(if i.val < 638 then
(if i.val < 637 then
590
else
719)
else
(if i.val < 639 then
766
else
(if i.val < 640 then
115
else
595))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
733
else
70)
else
(if i.val < 644 then
647
else
644))
else
(if i.val < 647 then
(if i.val < 646 then
588
else
91)
else
(if i.val < 648 then
643
else
95)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
56
else
691)
else
(if i.val < 652 then
746
else
111))
else
(if i.val < 655 then
(if i.val < 654 then
136
else
598)
else
(if i.val < 656 then
1068
else
(if i.val < 657 then
1072
else
672)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
658
else
572)
else
(if i.val < 661 then
579
else
775))
else
(if i.val < 664 then
(if i.val < 663 then
787
else
76)
else
(if i.val < 665 then
749
else
1065)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
613
else
777)
else
(if i.val < 669 then
67
else
735))
else
(if i.val < 672 then
(if i.val < 671 then
1075
else
780)
else
(if i.val < 673 then
657
else
(if i.val < 674 then
578
else
592))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
568
else
1079)
else
(if i.val < 678 then
716
else
556))
else
(if i.val < 681 then
(if i.val < 680 then
564
else
581)
else
(if i.val < 682 then
565
else
771)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
1066
else
689)
else
(if i.val < 686 then
685
else
794))
else
(if i.val < 689 then
(if i.val < 688 then
88
else
585)
else
(if i.val < 690 then
684
else
734))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
650
else
789)
else
(if i.val < 694 then
597
else
123))
else
(if i.val < 697 then
(if i.val < 696 then
58
else
542)
else
(if i.val < 698 then
104
else
703)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
137
else
539)
else
(if i.val < 702 then
561
else
577))
else
(if i.val < 705 then
(if i.val < 704 then
698
else
583)
else
(if i.val < 706 then
90
else
(if i.val < 707 then
548
else
783))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
120
else
633)
else
(if i.val < 711 then
772
else
584))
else
(if i.val < 714 then
(if i.val < 713 then
74
else
103)
else
(if i.val < 715 then
116
else
62)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
677
else
100)
else
(if i.val < 719 then
610
else
637))
else
(if i.val < 722 then
(if i.val < 721 then
544
else
594)
else
(if i.val < 723 then
764
else
(if i.val < 724 then
89
else
580)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
751
else
624)
else
(if i.val < 728 then
97
else
604))
else
(if i.val < 731 then
(if i.val < 730 then
81
else
753)
else
(if i.val < 732 then
586
else
732)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
641
else
690)
else
(if i.val < 736 then
669
else
541))
else
(if i.val < 739 then
(if i.val < 738 then
599
else
551)
else
(if i.val < 740 then
1071
else
(if i.val < 741 then
114
else
538)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
618
else
617)
else
(if i.val < 745 then
110
else
93))
else
(if i.val < 748 then
(if i.val < 747 then
651
else
68)
else
(if i.val < 749 then
559
else
664)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
121
else
725)
else
(if i.val < 753 then
614
else
730))
else
(if i.val < 756 then
(if i.val < 755 then
589
else
755)
else
(if i.val < 757 then
66
else
(if i.val < 758 then
785
else
758)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
609
else
101)
else
(if i.val < 762 then
628
else
767))
else
(if i.val < 765 then
(if i.val < 764 then
128
else
722)
else
(if i.val < 766 then
545
else
638)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
762
else
106)
else
(if i.val < 770 then
620
else
570))
else
(if i.val < 773 then
(if i.val < 772 then
682
else
710)
else
(if i.val < 774 then
135
else
(if i.val < 775 then
550
else
661))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
131
else
667)
else
(if i.val < 779 then
600
else
3))
else
(if i.val < 782 then
(if i.val < 781 then
671
else
792)
else
(if i.val < 783 then
1070
else
707)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
132
else
757)
else
(if i.val < 787 then
112
else
662))
else
(if i.val < 790 then
(if i.val < 789 then
537
else
692)
else
(if i.val < 791 then
98
else
(if i.val < 792 then
129
else
781)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
71
else
686)
else
(if i.val < 796 then
953
else
185))
else
(if i.val < 799 then
(if i.val < 798 then
932
else
281)
else
(if i.val < 800 then
284
else
800)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
857
else
875)
else
(if i.val < 804 then
936
else
209))
else
(if i.val < 807 then
(if i.val < 806 then
876
else
927)
else
(if i.val < 808 then
950
else
(if i.val < 809 then
895
else
977)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
179
else
879)
else
(if i.val < 813 then
958
else
961))
else
(if i.val < 816 then
(if i.val < 815 then
917
else
200)
else
(if i.val < 817 then
275
else
908)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
220
else
943)
else
(if i.val < 821 then
844
else
930))
else
(if i.val < 824 then
(if i.val < 823 then
255
else
970)
else
(if i.val < 825 then
843
else
282))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
197
else
251)
else
(if i.val < 829 then
860
else
918))
else
(if i.val < 832 then
(if i.val < 831 then
906
else
846)
else
(if i.val < 833 then
872
else
169)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
891
else
286)
else
(if i.val < 837 then
224
else
963))
else
(if i.val < 840 then
(if i.val < 839 then
256
else
180)
else
(if i.val < 841 then
175
else
(if i.val < 842 then
150
else
195))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
824
else
820)
else
(if i.val < 846 then
228
else
831))
else
(if i.val < 849 then
(if i.val < 848 then
248
else
294)
else
(if i.val < 850 then
190
else
213)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
241
else
931)
else
(if i.val < 854 then
201
else
155))
else
(if i.val < 857 then
(if i.val < 856 then
941
else
252)
else
(if i.val < 858 then
801
else
(if i.val < 859 then
954
else
153)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
828
else
909)
else
(if i.val < 863 then
888
else
243))
else
(if i.val < 866 then
(if i.val < 865 then
139
else
161)
else
(if i.val < 867 then
884
else
238)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
142
else
926)
else
(if i.val < 871 then
178
else
177))
else
(if i.val < 874 then
(if i.val < 873 then
832
else
957)
else
(if i.val < 875 then
199
else
(if i.val < 876 then
802
else
805)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
877
else
978)
else
(if i.val < 880 then
811
else
182))
else
(if i.val < 883 then
(if i.val < 882 then
278
else
272)
else
(if i.val < 884 then
885
else
866)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
883
else
249)
else
(if i.val < 888 then
889
else
862))
else
(if i.val < 891 then
(if i.val < 890 then
887
else
966)
else
(if i.val < 892 then
834
else
(if i.val < 893 then
184
else
156)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
152
else
808)
else
(if i.val < 897 then
898
else
173))
else
(if i.val < 900 then
(if i.val < 899 then
896
else
940)
else
(if i.val < 901 then
911
else
245)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
210
else
287)
else
(if i.val < 905 then
211
else
260))
else
(if i.val < 908 then
(if i.val < 907 then
830
else
11)
else
(if i.val < 909 then
817
else
(if i.val < 910 then
861
else
952))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
900
else
166)
else
(if i.val < 914 then
183
else
151))
else
(if i.val < 917 then
(if i.val < 916 then
230
else
206)
else
(if i.val < 918 then
814
else
829)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
202
else
140)
else
(if i.val < 922 then
929
else
138))
else
(if i.val < 925 then
(if i.val < 924 then
949
else
143)
else
(if i.val < 926 then
205
else
(if i.val < 927 then
869
else
806)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
259
else
921)
else
(if i.val < 931 then
821
else
852))
else
(if i.val < 934 then
(if i.val < 933 then
797
else
274)
else
(if i.val < 935 then
938
else
265)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
803
else
271)
else
(if i.val < 939 then
934
else
236))
else
(if i.val < 942 then
(if i.val < 941 then
899
else
855)
else
(if i.val < 943 then
5
else
(if i.val < 944 then
819
else
170))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
207
else
149)
else
(if i.val < 948 then
233
else
188))
else
(if i.val < 951 then
(if i.val < 950 then
923
else
807)
else
(if i.val < 952 then
222
else
910)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
795
else
858)
else
(if i.val < 956 then
226
else
960))
else
(if i.val < 959 then
(if i.val < 958 then
873
else
812)
else
(if i.val < 960 then
212
else
956))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
813
else
17)
else
(if i.val < 964 then
837
else
176))
else
(if i.val < 967 then
(if i.val < 966 then
225
else
890)
else
(if i.val < 968 then
269
else
193)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
203
else
823)
else
(if i.val < 972 then
196
else
975))
else
(if i.val < 975 then
(if i.val < 974 then
194
else
237)
else
(if i.val < 976 then
972
else
(if i.val < 977 then
976
else
809))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
878
else
270)
else
(if i.val < 981 then
231
else
187))
else
(if i.val < 984 then
(if i.val < 983 then
279
else
13)
else
(if i.val < 985 then
309
else
30)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
394
else
1057)
else
(if i.val < 989 then
361
else
1011))
else
(if i.val < 992 then
(if i.val < 991 then
499
else
1014)
else
(if i.val < 993 then
415
else
(if i.val < 994 then
336
else
463)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
395
else
1012)
else
(if i.val < 998 then
512
else
1048))
else
(if i.val < 1001 then
(if i.val < 1000 then
1056
else
359)
else
(if i.val < 1002 then
329
else
1002)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
342
else
420)
else
(if i.val < 1006 then
409
else
446))
else
(if i.val < 1009 then
(if i.val < 1008 then
419
else
1043)
else
(if i.val < 1010 then
522
else
(if i.val < 1011 then
35
else
989)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
996
else
366)
else
(if i.val < 1015 then
991
else
532))
else
(if i.val < 1018 then
(if i.val < 1017 then
369
else
373)
else
(if i.val < 1019 then
372
else
388)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
529
else
339)
else
(if i.val < 1023 then
31
else
398))
else
(if i.val < 1026 then
(if i.val < 1025 then
400
else
379)
else
(if i.val < 1027 then
481
else
(if i.val < 1028 then
1044
else
32)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
1042
else
390)
else
(if i.val < 1032 then
519
else
316))
else
(if i.val < 1035 then
(if i.val < 1034 then
417
else
384)
else
(if i.val < 1036 then
377
else
485)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
430
else
536)
else
(if i.val < 1040 then
533
else
364))
else
(if i.val < 1043 then
(if i.val < 1042 then
371
else
1029)
else
(if i.val < 1044 then
1008
else
(if i.val < 1045 then
1027
else
523))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
300
else
375)
else
(if i.val < 1049 then
998
else
406))
else
(if i.val < 1052 then
(if i.val < 1051 then
320
else
357)
else
(if i.val < 1053 then
36
else
317)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
37
else
319)
else
(if i.val < 1057 then
999
else
987))
else
(if i.val < 1060 then
(if i.val < 1059 then
520
else
426)
else
(if i.val < 1061 then
298
else
(if i.val < 1062 then
352
else
45)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
27
else
508)
else
(if i.val < 1066 then
665
else
683))
else
(if i.val < 1069 then
(if i.val < 1068 then
540
else
655)
else
(if i.val < 1070 then
601
else
782)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
739
else
656)
else
(if i.val < 1074 then
118
else
133))
else
(if i.val < 1077 then
(if i.val < 1076 then
670
else
79)
else
(if i.val < 1078 then
587
else
(if i.val < 1079 then
543
else
676)))))))))))

def g32p_row06_cosetBranchNext : Fin 3 → Fin 1080 → Fin 1080 :=
  ![g32p_row06_cosetBranchNextColumn0, g32p_row06_cosetBranchNextColumn1, g32p_row06_cosetBranchNextColumn2]

def g32p_row06_cosetBranchFactorColumn0 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
40
else
0)
else
(if i.val < 3 then
41
else
105))
else
(if i.val < 6 then
(if i.val < 5 then
16
else
81)
else
(if i.val < 7 then
58
else
60)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
5)
else
(if i.val < 11 then
40
else
93))
else
(if i.val < 14 then
(if i.val < 13 then
16
else
64)
else
(if i.val < 15 then
40
else
16))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
52
else
71)
else
(if i.val < 19 then
57
else
35))
else
(if i.val < 22 then
(if i.val < 21 then
57
else
86)
else
(if i.val < 23 then
86
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
112
else
0)
else
(if i.val < 27 then
87
else
142))
else
(if i.val < 30 then
(if i.val < 29 then
60
else
57)
else
(if i.val < 31 then
0
else
(if i.val < 32 then
1
else
81))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
60
else
0)
else
(if i.val < 36 then
25
else
109))
else
(if i.val < 39 then
(if i.val < 38 then
139
else
93)
else
(if i.val < 40 then
64
else
16)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
64
else
19)
else
(if i.val < 44 then
57
else
40))
else
(if i.val < 47 then
(if i.val < 46 then
64
else
16)
else
(if i.val < 48 then
52
else
(if i.val < 49 then
71
else
128)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
58
else
113)
else
(if i.val < 53 then
36
else
71))
else
(if i.val < 56 then
(if i.val < 55 then
81
else
0)
else
(if i.val < 57 then
23
else
23)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
72
else
35)
else
(if i.val < 61 then
57
else
86))
else
(if i.val < 64 then
(if i.val < 63 then
125
else
86)
else
(if i.val < 65 then
48
else
(if i.val < 66 then
10
else
57)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
93
else
68)
else
(if i.val < 70 then
23
else
0))
else
(if i.val < 73 then
(if i.val < 72 then
120
else
69)
else
(if i.val < 74 then
23
else
86)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
19
else
1)
else
(if i.val < 78 then
115
else
87))
else
(if i.val < 81 then
(if i.val < 80 then
142
else
57)
else
(if i.val < 82 then
0
else
(if i.val < 83 then
71
else
129)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
1
else
48))
else
(if i.val < 90 then
(if i.val < 89 then
57
else
57)
else
(if i.val < 91 then
64
else
93)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
57
else
0)
else
(if i.val < 95 then
0
else
81))
else
(if i.val < 98 then
(if i.val < 97 then
16
else
127)
else
(if i.val < 99 then
142
else
(if i.val < 100 then
64
else
53))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
48
else
93)
else
(if i.val < 104 then
64
else
16))
else
(if i.val < 107 then
(if i.val < 106 then
35
else
64)
else
(if i.val < 108 then
143
else
139)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
3
else
27)
else
(if i.val < 112 then
64
else
64))
else
(if i.val < 115 then
(if i.val < 114 then
25
else
109)
else
(if i.val < 116 then
139
else
(if i.val < 117 then
64
else
64)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
64
else
40)
else
(if i.val < 121 then
64
else
64))
else
(if i.val < 124 then
(if i.val < 123 then
143
else
128)
else
(if i.val < 125 then
87
else
86)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
40
else
71)
else
(if i.val < 129 then
81
else
71))
else
(if i.val < 132 then
(if i.val < 131 then
57
else
81)
else
(if i.val < 133 then
105
else
(if i.val < 134 then
115
else
143))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
87
else
127)
else
(if i.val < 138 then
33
else
92))
else
(if i.val < 141 then
(if i.val < 140 then
23
else
0)
else
(if i.val < 142 then
47
else
60)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
62
else
23)
else
(if i.val < 146 then
35
else
15))
else
(if i.val < 149 then
(if i.val < 148 then
52
else
35)
else
(if i.val < 150 then
52
else
23))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
35
else
86)
else
(if i.val < 154 then
64
else
86))
else
(if i.val < 157 then
(if i.val < 156 then
5
else
125)
else
(if i.val < 158 then
86
else
36)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
83
else
48)
else
(if i.val < 162 then
0
else
112))
else
(if i.val < 165 then
(if i.val < 164 then
87
else
120)
else
(if i.val < 166 then
93
else
(if i.val < 167 then
59
else
86))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
115
else
2)
else
(if i.val < 171 then
11
else
0))
else
(if i.val < 174 then
(if i.val < 173 then
68
else
0)
else
(if i.val < 175 then
0
else
120)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
64
else
15)
else
(if i.val < 179 then
41
else
10))
else
(if i.val < 182 then
(if i.val < 181 then
129
else
0)
else
(if i.val < 183 then
36
else
(if i.val < 184 then
1
else
10)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
93
else
115)
else
(if i.val < 188 then
23
else
0))
else
(if i.val < 191 then
(if i.val < 190 then
64
else
87)
else
(if i.val < 192 then
1
else
115)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
87
else
57)
else
(if i.val < 196 then
0
else
23))
else
(if i.val < 199 then
(if i.val < 198 then
87
else
86)
else
(if i.val < 200 then
0
else
(if i.val < 201 then
120
else
48)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
0
else
16)
else
(if i.val < 205 then
57
else
0))
else
(if i.val < 208 then
(if i.val < 207 then
0
else
0)
else
(if i.val < 209 then
1
else
1)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
60
else
23)
else
(if i.val < 213 then
18
else
125))
else
(if i.val < 216 then
(if i.val < 215 then
18
else
64)
else
(if i.val < 217 then
93
else
(if i.val < 218 then
93
else
64)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
57
else
8)
else
(if i.val < 222 then
57
else
93))
else
(if i.val < 225 then
(if i.val < 224 then
0
else
57)
else
(if i.val < 226 then
120
else
57)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
127
else
127)
else
(if i.val < 230 then
93
else
64))
else
(if i.val < 233 then
(if i.val < 232 then
16
else
142)
else
(if i.val < 234 then
33
else
(if i.val < 235 then
8
else
139))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
69
else
27)
else
(if i.val < 239 then
93
else
139))
else
(if i.val < 242 then
(if i.val < 241 then
64
else
64)
else
(if i.val < 243 then
109
else
64)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
64
else
16)
else
(if i.val < 247 then
64
else
138))
else
(if i.val < 250 then
(if i.val < 249 then
86
else
62)
else
(if i.val < 251 then
71
else
(if i.val < 252 then
57
else
125)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
115
else
127)
else
(if i.val < 256 then
106
else
45))
else
(if i.val < 259 then
(if i.val < 258 then
33
else
64)
else
(if i.val < 260 then
64
else
64)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
25
else
127)
else
(if i.val < 264 then
64
else
35))
else
(if i.val < 267 then
(if i.val < 266 then
64
else
125)
else
(if i.val < 268 then
139
else
(if i.val < 269 then
25
else
64)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
5
else
64)
else
(if i.val < 273 then
64
else
58))
else
(if i.val < 276 then
(if i.val < 275 then
113
else
16)
else
(if i.val < 277 then
71
else
57)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
7
else
142)
else
(if i.val < 281 then
139
else
87))
else
(if i.val < 284 then
(if i.val < 283 then
87
else
128)
else
(if i.val < 285 then
128
else
143))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
125
else
25)
else
(if i.val < 289 then
113
else
52))
else
(if i.val < 292 then
(if i.val < 291 then
35
else
115)
else
(if i.val < 293 then
81
else
33)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
33
else
68)
else
(if i.val < 297 then
19
else
11))
else
(if i.val < 300 then
(if i.val < 299 then
36
else
68)
else
(if i.val < 301 then
0
else
(if i.val < 302 then
88
else
47))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
60
else
84)
else
(if i.val < 306 then
7
else
50))
else
(if i.val < 309 then
(if i.val < 308 then
62
else
2)
else
(if i.val < 310 then
35
else
69)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
143
else
35)
else
(if i.val < 314 then
92
else
138))
else
(if i.val < 317 then
(if i.val < 316 then
36
else
62)
else
(if i.val < 318 then
52
else
(if i.val < 319 then
92
else
0)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
47
else
7)
else
(if i.val < 323 then
62
else
52))
else
(if i.val < 326 then
(if i.val < 325 then
35
else
83)
else
(if i.val < 327 then
23
else
72)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
64
else
86)
else
(if i.val < 331 then
29
else
41))
else
(if i.val < 334 then
(if i.val < 333 then
86
else
35)
else
(if i.val < 335 then
83
else
(if i.val < 336 then
105
else
83)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
58
else
105)
else
(if i.val < 340 then
83
else
86))
else
(if i.val < 343 then
(if i.val < 342 then
86
else
16)
else
(if i.val < 344 then
74
else
23)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
23
else
120)
else
(if i.val < 348 then
93
else
87))
else
(if i.val < 351 then
(if i.val < 350 then
86
else
120)
else
(if i.val < 352 then
64
else
(if i.val < 353 then
16
else
64)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
10
else
84)
else
(if i.val < 357 then
59
else
36))
else
(if i.val < 360 then
(if i.val < 359 then
10
else
23)
else
(if i.val < 361 then
55
else
11)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
86
else
72)
else
(if i.val < 365 then
69
else
58))
else
(if i.val < 368 then
(if i.val < 367 then
0
else
0)
else
(if i.val < 369 then
92
else
(if i.val < 370 then
36
else
0))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
68
else
57)
else
(if i.val < 374 then
62
else
1))
else
(if i.val < 377 then
(if i.val < 376 then
64
else
40)
else
(if i.val < 378 then
20
else
74)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
115
else
120)
else
(if i.val < 382 then
44
else
86))
else
(if i.val < 385 then
(if i.val < 384 then
62
else
71)
else
(if i.val < 386 then
110
else
(if i.val < 387 then
57
else
0)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
76
else
1)
else
(if i.val < 391 then
1
else
60))
else
(if i.val < 394 then
(if i.val < 393 then
87
else
93)
else
(if i.val < 395 then
120
else
115)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
55
else
52)
else
(if i.val < 399 then
11
else
10))
else
(if i.val < 402 then
(if i.val < 401 then
88
else
0)
else
(if i.val < 403 then
10
else
(if i.val < 404 then
93
else
115))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
86
else
87)
else
(if i.val < 408 then
35
else
86))
else
(if i.val < 411 then
(if i.val < 410 then
0
else
57)
else
(if i.val < 412 then
16
else
57)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
0
else
48)
else
(if i.val < 416 then
40
else
1))
else
(if i.val < 419 then
(if i.val < 418 then
60
else
16)
else
(if i.val < 420 then
73
else
125))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
1
else
93)
else
(if i.val < 424 then
68
else
0))
else
(if i.val < 427 then
(if i.val < 426 then
86
else
57)
else
(if i.val < 428 then
57
else
48)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
35
else
86)
else
(if i.val < 432 then
18
else
55))
else
(if i.val < 435 then
(if i.val < 434 then
64
else
86)
else
(if i.val < 436 then
5
else
(if i.val < 437 then
36
else
51))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
93
else
115)
else
(if i.val < 441 then
55
else
64))
else
(if i.val < 444 then
(if i.val < 443 then
87
else
93)
else
(if i.val < 445 then
102
else
5)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
129
else
86)
else
(if i.val < 449 then
0
else
8))
else
(if i.val < 452 then
(if i.val < 451 then
57
else
0)
else
(if i.val < 453 then
138
else
(if i.val < 454 then
57
else
125)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
11
else
93)
else
(if i.val < 458 then
57
else
33))
else
(if i.val < 461 then
(if i.val < 460 then
129
else
127)
else
(if i.val < 462 then
120
else
93)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
139
else
138)
else
(if i.val < 466 then
64
else
40))
else
(if i.val < 469 then
(if i.val < 468 then
16
else
71)
else
(if i.val < 470 then
57
else
(if i.val < 471 then
81
else
72)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
127
else
106)
else
(if i.val < 475 then
35
else
64))
else
(if i.val < 478 then
(if i.val < 477 then
125
else
25)
else
(if i.val < 479 then
64
else
31)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
58
else
81)
else
(if i.val < 483 then
71
else
57))
else
(if i.val < 486 then
(if i.val < 485 then
142
else
19)
else
(if i.val < 487 then
87
else
(if i.val < 488 then
27
else
101)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
124
else
125)
else
(if i.val < 492 then
35
else
106))
else
(if i.val < 495 then
(if i.val < 494 then
64
else
64)
else
(if i.val < 496 then
64
else
57)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
142
else
10)
else
(if i.val < 500 then
10
else
22))
else
(if i.val < 503 then
(if i.val < 502 then
64
else
16)
else
(if i.val < 504 then
127
else
(if i.val < 505 then
106
else
86))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
128
else
64)
else
(if i.val < 509 then
88
else
48))
else
(if i.val < 512 then
(if i.val < 511 then
53
else
143)
else
(if i.val < 513 then
139
else
38)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
139
else
71)
else
(if i.val < 517 then
106
else
69))
else
(if i.val < 520 then
(if i.val < 519 then
28
else
125)
else
(if i.val < 521 then
58
else
(if i.val < 522 then
40
else
33)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
3
else
143)
else
(if i.val < 526 then
83
else
81))
else
(if i.val < 529 then
(if i.val < 528 then
40
else
47)
else
(if i.val < 530 then
86
else
125)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
106
else
109)
else
(if i.val < 534 then
83
else
103))
else
(if i.val < 537 then
(if i.val < 536 then
36
else
10)
else
(if i.val < 538 then
19
else
(if i.val < 539 then
36
else
55))))))))))
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
11
else
29)
else
(if i.val < 543 then
121
else
64))
else
(if i.val < 546 then
(if i.val < 545 then
52
else
73)
else
(if i.val < 547 then
0
else
92)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
36
else
0)
else
(if i.val < 551 then
129
else
7))
else
(if i.val < 554 then
(if i.val < 553 then
50
else
62)
else
(if i.val < 555 then
2
else
23))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
143
else
7)
else
(if i.val < 559 then
2
else
21))
else
(if i.val < 562 then
(if i.val < 561 then
81
else
86)
else
(if i.val < 563 then
62
else
47)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
23
else
116)
else
(if i.val < 567 then
136
else
28))
else
(if i.val < 570 then
(if i.val < 569 then
40
else
143)
else
(if i.val < 571 then
143
else
(if i.val < 572 then
68
else
38))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
90
else
86)
else
(if i.val < 576 then
62
else
122))
else
(if i.val < 579 then
(if i.val < 578 then
11
else
0)
else
(if i.val < 580 then
35
else
143)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
52
else
138)
else
(if i.val < 584 then
40
else
55))
else
(if i.val < 587 then
(if i.val < 586 then
92
else
0)
else
(if i.val < 588 then
47
else
(if i.val < 589 then
84
else
52)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
62
else
120)
else
(if i.val < 593 then
138
else
35))
else
(if i.val < 596 then
(if i.val < 595 then
92
else
84)
else
(if i.val < 597 then
73
else
52)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
35
else
72)
else
(if i.val < 601 then
86
else
35))
else
(if i.val < 604 then
(if i.val < 603 then
83
else
48)
else
(if i.val < 605 then
105
else
(if i.val < 606 then
83
else
86)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
83
else
83)
else
(if i.val < 610 then
7
else
57))
else
(if i.val < 613 then
(if i.val < 612 then
51
else
125)
else
(if i.val < 614 then
83
else
83)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
83
else
36)
else
(if i.val < 618 then
113
else
105))
else
(if i.val < 621 then
(if i.val < 620 then
109
else
128)
else
(if i.val < 622 then
127
else
(if i.val < 623 then
88
else
108)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
64
else
88)
else
(if i.val < 627 then
41
else
10))
else
(if i.val < 630 then
(if i.val < 629 then
36
else
10)
else
(if i.val < 631 then
93
else
39)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
62
else
64)
else
(if i.val < 635 then
35
else
64))
else
(if i.val < 638 then
(if i.val < 637 then
11
else
115)
else
(if i.val < 639 then
41
else
(if i.val < 640 then
86
else
62))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
59
else
98)
else
(if i.val < 644 then
76
else
87))
else
(if i.val < 647 then
(if i.val < 646 then
41
else
52)
else
(if i.val < 648 then
11
else
56)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
23
else
0)
else
(if i.val < 652 then
138
else
11))
else
(if i.val < 655 then
(if i.val < 654 then
29
else
5)
else
(if i.val < 656 then
72
else
(if i.val < 657 then
87
else
126)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
72
else
58)
else
(if i.val < 661 then
71
else
0))
else
(if i.val < 664 then
(if i.val < 663 then
0
else
72)
else
(if i.val < 665 then
0
else
1)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
62
else
22)
else
(if i.val < 669 then
44
else
1))
else
(if i.val < 672 then
(if i.val < 671 then
20
else
20)
else
(if i.val < 673 then
35
else
(if i.val < 674 then
115
else
57))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
120
else
92)
else
(if i.val < 678 then
48
else
115))
else
(if i.val < 681 then
(if i.val < 680 then
29
else
88)
else
(if i.val < 682 then
106
else
125)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
36
else
76)
else
(if i.val < 686 then
57
else
127))
else
(if i.val < 689 then
(if i.val < 688 then
36
else
52)
else
(if i.val < 690 then
0
else
138))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
1
else
138)
else
(if i.val < 694 then
110
else
57))
else
(if i.val < 697 then
(if i.val < 696 then
76
else
1)
else
(if i.val < 698 then
1
else
109)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
87
else
55)
else
(if i.val < 702 then
52
else
11))
else
(if i.val < 705 then
(if i.val < 704 then
34
else
0)
else
(if i.val < 706 then
57
else
(if i.val < 707 then
60
else
40))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
1
else
16)
else
(if i.val < 711 then
73
else
86))
else
(if i.val < 714 then
(if i.val < 713 then
1
else
0)
else
(if i.val < 715 then
86
else
7)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
27
else
0)
else
(if i.val < 719 then
81
else
33))
else
(if i.val < 722 then
(if i.val < 721 then
60
else
125)
else
(if i.val < 723 then
125
else
(if i.val < 724 then
92
else
33)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
128
else
1)
else
(if i.val < 728 then
139
else
92))
else
(if i.val < 731 then
(if i.val < 730 then
136
else
10)
else
(if i.val < 732 then
83
else
23)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
83
else
64)
else
(if i.val < 736 then
5
else
10))
else
(if i.val < 739 then
(if i.val < 738 then
93
else
129)
else
(if i.val < 740 then
61
else
(if i.val < 741 then
86
else
35)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
57
else
5)
else
(if i.val < 745 then
117
else
60))
else
(if i.val < 748 then
(if i.val < 747 then
86
else
5)
else
(if i.val < 749 then
30
else
68)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
64
else
102)
else
(if i.val < 753 then
127
else
71))
else
(if i.val < 756 then
(if i.val < 755 then
57
else
137)
else
(if i.val < 757 then
25
else
(if i.val < 758 then
142
else
142)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
50
else
125)
else
(if i.val < 762 then
64
else
138))
else
(if i.val < 765 then
(if i.val < 764 then
138
else
19)
else
(if i.val < 766 then
25
else
27)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
53
else
83)
else
(if i.val < 770 then
25
else
28))
else
(if i.val < 773 then
(if i.val < 772 then
19
else
125)
else
(if i.val < 774 then
81
else
(if i.val < 775 then
43
else
125))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
106
else
83)
else
(if i.val < 779 then
36
else
106))
else
(if i.val < 782 then
(if i.val < 781 then
57
else
93)
else
(if i.val < 783 then
120
else
113)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
101
else
128)
else
(if i.val < 787 then
143
else
40))
else
(if i.val < 790 then
(if i.val < 789 then
83
else
137)
else
(if i.val < 791 then
92
else
(if i.val < 792 then
118
else
106)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
25
else
81)
else
(if i.val < 796 then
11
else
116))
else
(if i.val < 799 then
(if i.val < 798 then
56
else
69)
else
(if i.val < 800 then
57
else
11)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
0
else
11)
else
(if i.val < 804 then
29
else
93))
else
(if i.val < 807 then
(if i.val < 806 then
119
else
136)
else
(if i.val < 808 then
64
else
(if i.val < 809 then
136
else
126)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
60
else
58)
else
(if i.val < 813 then
59
else
76))
else
(if i.val < 816 then
(if i.val < 815 then
136
else
23)
else
(if i.val < 817 then
0
else
0)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
1
else
1)
else
(if i.val < 821 then
50
else
11))
else
(if i.val < 824 then
(if i.val < 823 then
23
else
16)
else
(if i.val < 825 then
18
else
81))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
62
else
47)
else
(if i.val < 829 then
2
else
2))
else
(if i.val < 832 then
(if i.val < 831 then
68
else
48)
else
(if i.val < 833 then
23
else
23)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
21
else
2)
else
(if i.val < 837 then
50
else
72))
else
(if i.val < 840 then
(if i.val < 839 then
2
else
81)
else
(if i.val < 841 then
35
else
(if i.val < 842 then
64
else
113))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
7
else
84)
else
(if i.val < 846 then
56
else
143))
else
(if i.val < 849 then
(if i.val < 848 then
58
else
84)
else
(if i.val < 850 then
143
else
18)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
2
else
52)
else
(if i.val < 854 then
143
else
11))
else
(if i.val < 857 then
(if i.val < 856 then
10
else
52)
else
(if i.val < 858 then
35
else
(if i.val < 859 then
83
else
55)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
11
else
0)
else
(if i.val < 863 then
80
else
2))
else
(if i.val < 866 then
(if i.val < 865 then
22
else
83)
else
(if i.val < 867 then
122
else
120)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
35
else
143)
else
(if i.val < 871 then
83
else
138))
else
(if i.val < 874 then
(if i.val < 873 then
40
else
138)
else
(if i.val < 875 then
84
else
(if i.val < 876 then
52
else
62)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
29
else
35)
else
(if i.val < 880 then
105
else
86))
else
(if i.val < 883 then
(if i.val < 882 then
16
else
74)
else
(if i.val < 884 then
138
else
89)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
125
else
83)
else
(if i.val < 888 then
35
else
83))
else
(if i.val < 891 then
(if i.val < 890 then
105
else
142)
else
(if i.val < 892 then
36
else
(if i.val < 893 then
115
else
19)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
80
else
125)
else
(if i.val < 897 then
46
else
138))
else
(if i.val < 900 then
(if i.val < 899 then
83
else
51)
else
(if i.val < 901 then
113
else
59)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
25
else
26)
else
(if i.val < 905 then
92
else
64))
else
(if i.val < 908 then
(if i.val < 907 then
40
else
49)
else
(if i.val < 909 then
88
else
(if i.val < 910 then
87
else
64))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
120
else
64)
else
(if i.val < 914 then
55
else
62))
else
(if i.val < 917 then
(if i.val < 916 then
74
else
29)
else
(if i.val < 918 then
92
else
79)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
89
else
52)
else
(if i.val < 922 then
58
else
62))
else
(if i.val < 925 then
(if i.val < 924 then
56
else
64)
else
(if i.val < 926 then
2
else
(if i.val < 927 then
58
else
11)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
55
else
72)
else
(if i.val < 931 then
58
else
30))
else
(if i.val < 934 then
(if i.val < 933 then
116
else
26)
else
(if i.val < 935 then
0
else
93)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
114
else
44)
else
(if i.val < 939 then
48
else
22))
else
(if i.val < 942 then
(if i.val < 941 then
16
else
75)
else
(if i.val < 943 then
34
else
(if i.val < 944 then
113
else
6))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
48
else
41)
else
(if i.val < 948 then
68
else
43))
else
(if i.val < 951 then
(if i.val < 950 then
27
else
127)
else
(if i.val < 952 then
129
else
88)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
1
else
8)
else
(if i.val < 956 then
72
else
77))
else
(if i.val < 959 then
(if i.val < 958 then
58
else
138)
else
(if i.val < 960 then
16
else
73))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
0
else
0)
else
(if i.val < 964 then
125
else
67))
else
(if i.val < 967 then
(if i.val < 966 then
28
else
33)
else
(if i.val < 968 then
68
else
86)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
83
else
87)
else
(if i.val < 972 then
35
else
93))
else
(if i.val < 975 then
(if i.val < 974 then
86
else
65)
else
(if i.val < 976 then
92
else
(if i.val < 977 then
138
else
124))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
51
else
92)
else
(if i.val < 981 then
106
else
118))
else
(if i.val < 984 then
(if i.val < 983 then
138
else
0)
else
(if i.val < 985 then
138
else
47)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
29
else
2)
else
(if i.val < 989 then
68
else
23))
else
(if i.val < 992 then
(if i.val < 991 then
7
else
64)
else
(if i.val < 993 then
66
else
(if i.val < 994 then
46
else
70)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
136
else
19)
else
(if i.val < 998 then
83
else
30))
else
(if i.val < 1001 then
(if i.val < 1000 then
49
else
52)
else
(if i.val < 1002 then
0
else
71)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
19
else
2)
else
(if i.val < 1006 then
125
else
60))
else
(if i.val < 1009 then
(if i.val < 1008 then
23
else
40)
else
(if i.val < 1010 then
50
else
(if i.val < 1011 then
56
else
81)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
18
else
2)
else
(if i.val < 1015 then
90
else
50))
else
(if i.val < 1018 then
(if i.val < 1017 then
136
else
35)
else
(if i.val < 1019 then
90
else
2)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
16
else
143)
else
(if i.val < 1023 then
2
else
143))
else
(if i.val < 1026 then
(if i.val < 1025 then
38
else
119)
else
(if i.val < 1027 then
2
else
(if i.val < 1028 then
51
else
78)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
30
else
132)
else
(if i.val < 1032 then
5
else
122))
else
(if i.val < 1035 then
(if i.val < 1034 then
7
else
67)
else
(if i.val < 1036 then
138
else
131)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
16
else
2)
else
(if i.val < 1040 then
138
else
138))
else
(if i.val < 1043 then
(if i.val < 1042 then
29
else
35)
else
(if i.val < 1044 then
36
else
(if i.val < 1045 then
64
else
10))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
50
else
64)
else
(if i.val < 1049 then
36
else
92))
else
(if i.val < 1052 then
(if i.val < 1051 then
58
else
1)
else
(if i.val < 1053 then
20
else
121)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
110
else
41)
else
(if i.val < 1057 then
1
else
87))
else
(if i.val < 1060 then
(if i.val < 1059 then
127
else
15)
else
(if i.val < 1061 then
6
else
(if i.val < 1062 then
22
else
87)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
67
else
81)
else
(if i.val < 1066 then
68
else
41))
else
(if i.val < 1069 then
(if i.val < 1068 then
56
else
82)
else
(if i.val < 1070 then
78
else
7)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
1
else
18)
else
(if i.val < 1074 then
92
else
120))
else
(if i.val < 1077 then
(if i.val < 1076 then
10
else
64)
else
(if i.val < 1078 then
36
else
(if i.val < 1079 then
110
else
66)))))))))))

def g32p_row06_cosetBranchFactorColumn1 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 540 then
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
0
else
0))
else
(if i.val < 6 then
(if i.val < 5 then
65
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
65
else
87)
else
(if i.val < 15 then
87
else
60))))
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
76
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
87
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
60
else
0)
else
(if i.val < 31 then
0
else
(if i.val < 32 then
0
else
0))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
0
else
0)
else
(if i.val < 36 then
0
else
0))
else
(if i.val < 39 then
(if i.val < 38 then
65
else
87)
else
(if i.val < 40 then
87
else
60)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
0
else
0)
else
(if i.val < 44 then
76
else
108))
else
(if i.val < 47 then
(if i.val < 46 then
5
else
5)
else
(if i.val < 48 then
27
else
(if i.val < 49 then
1
else
0)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
26
else
127)
else
(if i.val < 53 then
0
else
1))
else
(if i.val < 56 then
(if i.val < 55 then
48
else
0)
else
(if i.val < 57 then
0
else
0)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
0
else
87)
else
(if i.val < 61 then
88
else
60))
else
(if i.val < 64 then
(if i.val < 63 then
0
else
0)
else
(if i.val < 65 then
0
else
(if i.val < 66 then
0
else
0)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
0
else
0)
else
(if i.val < 70 then
0
else
0))
else
(if i.val < 73 then
(if i.val < 72 then
0
else
0)
else
(if i.val < 74 then
0
else
0)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
0
else
0)
else
(if i.val < 78 then
0
else
0))
else
(if i.val < 81 then
(if i.val < 80 then
0
else
27)
else
(if i.val < 82 then
0
else
(if i.val < 83 then
0
else
0)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
0
else
2))
else
(if i.val < 90 then
(if i.val < 89 then
0
else
0)
else
(if i.val < 91 then
0
else
87)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
0
else
0)
else
(if i.val < 95 then
0
else
0))
else
(if i.val < 98 then
(if i.val < 97 then
0
else
0)
else
(if i.val < 99 then
87
else
(if i.val < 100 then
0
else
0))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
76
else
108)
else
(if i.val < 104 then
5
else
5))
else
(if i.val < 107 then
(if i.val < 106 then
1
else
0)
else
(if i.val < 108 then
26
else
127)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
0
else
1)
else
(if i.val < 112 then
88
else
60))
else
(if i.val < 115 then
(if i.val < 114 then
121
else
87)
else
(if i.val < 116 then
72
else
(if i.val < 117 then
50
else
66)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
25
else
88)
else
(if i.val < 121 then
72
else
11))
else
(if i.val < 124 then
(if i.val < 123 then
66
else
7)
else
(if i.val < 125 then
87
else
1)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
19
else
48)
else
(if i.val < 129 then
73
else
26))
else
(if i.val < 132 then
(if i.val < 131 then
27
else
68)
else
(if i.val < 133 then
55
else
(if i.val < 134 then
1
else
63))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
108
else
68)
else
(if i.val < 138 then
104
else
0))
else
(if i.val < 141 then
(if i.val < 140 then
0
else
0)
else
(if i.val < 142 then
0
else
0)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
65
else
0)
else
(if i.val < 146 then
88
else
60))
else
(if i.val < 149 then
(if i.val < 148 then
0
else
0)
else
(if i.val < 150 then
0
else
0))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
5
else
5)
else
(if i.val < 154 then
0
else
88))
else
(if i.val < 157 then
(if i.val < 156 then
0
else
0)
else
(if i.val < 158 then
127
else
0)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
0
else
68)
else
(if i.val < 162 then
0
else
0))
else
(if i.val < 165 then
(if i.val < 164 then
0
else
0)
else
(if i.val < 166 then
0
else
(if i.val < 167 then
0
else
0))))))
else
(if i.val < 185 then
(if i.val < 176 then
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
0)))
else
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
(if i.val < 184 then
0
else
88)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
60
else
0)
else
(if i.val < 188 then
87
else
0))
else
(if i.val < 191 then
(if i.val < 190 then
27
else
0)
else
(if i.val < 192 then
0
else
0)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
72
else
7)
else
(if i.val < 196 then
0
else
7))
else
(if i.val < 199 then
(if i.val < 198 then
87
else
1)
else
(if i.val < 200 then
40
else
(if i.val < 201 then
48
else
73)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
0
else
0)
else
(if i.val < 205 then
0
else
55))
else
(if i.val < 208 then
(if i.val < 207 then
0
else
0)
else
(if i.val < 209 then
108
else
0)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
104
else
0)
else
(if i.val < 213 then
87
else
0))
else
(if i.val < 216 then
(if i.val < 215 then
0
else
0)
else
(if i.val < 217 then
0
else
(if i.val < 218 then
0
else
0)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
27
else
0)
else
(if i.val < 222 then
0
else
0))
else
(if i.val < 225 then
(if i.val < 224 then
0
else
0)
else
(if i.val < 226 then
0
else
0)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
0
else
0)
else
(if i.val < 230 then
108
else
5))
else
(if i.val < 233 then
(if i.val < 232 then
5
else
1)
else
(if i.val < 234 then
0
else
(if i.val < 235 then
26
else
127))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
0
else
1)
else
(if i.val < 239 then
121
else
72))
else
(if i.val < 242 then
(if i.val < 241 then
66
else
25)
else
(if i.val < 243 then
88
else
72)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
11
else
66)
else
(if i.val < 247 then
7
else
87))
else
(if i.val < 250 then
(if i.val < 249 then
1
else
19)
else
(if i.val < 251 then
26
else
(if i.val < 252 then
27
else
68)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
1
else
63)
else
(if i.val < 256 then
108
else
68))
else
(if i.val < 259 then
(if i.val < 258 then
104
else
5)
else
(if i.val < 260 then
33
else
55)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
33
else
139)
else
(if i.val < 264 then
27
else
55))
else
(if i.val < 267 then
(if i.val < 266 then
120
else
86)
else
(if i.val < 268 then
48
else
(if i.val < 269 then
87
else
65)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
9
else
76)
else
(if i.val < 273 then
65
else
11))
else
(if i.val < 276 then
(if i.val < 275 then
25
else
23)
else
(if i.val < 277 then
126
else
29)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
48
else
66)
else
(if i.val < 281 then
141
else
40))
else
(if i.val < 284 then
(if i.val < 283 then
48
else
47)
else
(if i.val < 285 then
26
else
11))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
40
else
33)
else
(if i.val < 289 then
125
else
86))
else
(if i.val < 292 then
(if i.val < 291 then
108
else
76)
else
(if i.val < 293 then
1
else
27)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
62
else
0)
else
(if i.val < 297 then
0
else
0))
else
(if i.val < 300 then
(if i.val < 299 then
0
else
0)
else
(if i.val < 301 then
0
else
(if i.val < 302 then
0
else
0))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
0
else
65)
else
(if i.val < 306 then
88
else
125))
else
(if i.val < 309 then
(if i.val < 308 then
0
else
0)
else
(if i.val < 310 then
0
else
0)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
5
else
0)
else
(if i.val < 314 then
0
else
56))
else
(if i.val < 317 then
(if i.val < 316 then
127
else
0)
else
(if i.val < 318 then
0
else
(if i.val < 319 then
88
else
5)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
0
else
87)
else
(if i.val < 323 then
65
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
66
else
5)
else
(if i.val < 327 then
0
else
72)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
7
else
0)
else
(if i.val < 331 then
7
else
87))
else
(if i.val < 334 then
(if i.val < 333 then
127
else
40)
else
(if i.val < 335 then
48
else
(if i.val < 336 then
88
else
0)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
139
else
0)
else
(if i.val < 340 then
11
else
58))
else
(if i.val < 343 then
(if i.val < 342 then
63
else
108)
else
(if i.val < 344 then
94
else
104)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
0
else
0)
else
(if i.val < 348 then
0
else
0))
else
(if i.val < 351 then
(if i.val < 350 then
0
else
0)
else
(if i.val < 352 then
0
else
(if i.val < 353 then
0
else
0)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
0
else
0)
else
(if i.val < 357 then
0
else
0))
else
(if i.val < 360 then
(if i.val < 359 then
0
else
0)
else
(if i.val < 361 then
0
else
0)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
0
else
0)
else
(if i.val < 365 then
0
else
0))
else
(if i.val < 368 then
(if i.val < 367 then
0
else
0)
else
(if i.val < 369 then
0
else
(if i.val < 370 then
0
else
0))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
0
else
0)
else
(if i.val < 374 then
0
else
0))
else
(if i.val < 377 then
(if i.val < 376 then
0
else
0)
else
(if i.val < 378 then
0
else
0)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
0
else
0)
else
(if i.val < 382 then
0
else
0))
else
(if i.val < 385 then
(if i.val < 384 then
0
else
0)
else
(if i.val < 386 then
0
else
(if i.val < 387 then
0
else
0)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
0
else
0)
else
(if i.val < 391 then
0
else
0))
else
(if i.val < 394 then
(if i.val < 393 then
88
else
7)
else
(if i.val < 395 then
88
else
33)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
61
else
76)
else
(if i.val < 399 then
0
else
120))
else
(if i.val < 402 then
(if i.val < 401 then
86
else
48)
else
(if i.val < 403 then
87
else
(if i.val < 404 then
5
else
88))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
7
else
115)
else
(if i.val < 408 then
11
else
0))
else
(if i.val < 411 then
(if i.val < 410 then
23
else
103)
else
(if i.val < 412 then
7
else
48)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
0
else
139)
else
(if i.val < 416 then
108
else
48))
else
(if i.val < 419 then
(if i.val < 418 then
40
else
0)
else
(if i.val < 420 then
0
else
0))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
71
else
125)
else
(if i.val < 424 then
86
else
19))
else
(if i.val < 427 then
(if i.val < 426 then
76
else
1)
else
(if i.val < 428 then
27
else
62)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
0
else
0)
else
(if i.val < 432 then
0
else
5))
else
(if i.val < 435 then
(if i.val < 434 then
0
else
88)
else
(if i.val < 436 then
0
else
(if i.val < 437 then
0
else
0))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
60
else
0)
else
(if i.val < 441 then
0
else
27))
else
(if i.val < 444 then
(if i.val < 443 then
0
else
0)
else
(if i.val < 445 then
0
else
0)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
87
else
1)
else
(if i.val < 449 then
40
else
0))
else
(if i.val < 452 then
(if i.val < 451 then
0
else
0)
else
(if i.val < 453 then
108
else
(if i.val < 454 then
0
else
0)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
0
else
0)
else
(if i.val < 458 then
27
else
0))
else
(if i.val < 461 then
(if i.val < 460 then
0
else
0)
else
(if i.val < 462 then
0
else
121)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
72
else
66)
else
(if i.val < 466 then
25
else
88))
else
(if i.val < 469 then
(if i.val < 468 then
66
else
26)
else
(if i.val < 470 then
27
else
(if i.val < 471 then
68
else
1)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
63
else
68)
else
(if i.val < 475 then
55
else
120))
else
(if i.val < 478 then
(if i.val < 477 then
86
else
87)
else
(if i.val < 479 then
65
else
65)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
11
else
25)
else
(if i.val < 483 then
126
else
29))
else
(if i.val < 486 then
(if i.val < 485 then
66
else
141)
else
(if i.val < 487 then
40
else
(if i.val < 488 then
47
else
26)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
11
else
40)
else
(if i.val < 492 then
108
else
1))
else
(if i.val < 495 then
(if i.val < 494 then
58
else
106)
else
(if i.val < 496 then
11
else
28)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
1
else
10)
else
(if i.val < 500 then
1
else
1))
else
(if i.val < 503 then
(if i.val < 502 then
5
else
1)
else
(if i.val < 504 then
21
else
(if i.val < 505 then
40
else
2))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
73
else
107)
else
(if i.val < 509 then
107
else
11))
else
(if i.val < 512 then
(if i.val < 511 then
58
else
11)
else
(if i.val < 513 then
80
else
2)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
37
else
84)
else
(if i.val < 517 then
2
else
72))
else
(if i.val < 520 then
(if i.val < 519 then
68
else
48)
else
(if i.val < 521 then
86
else
(if i.val < 522 then
43
else
33)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
62
else
34)
else
(if i.val < 526 then
26
else
92))
else
(if i.val < 529 then
(if i.val < 528 then
32
else
48)
else
(if i.val < 530 then
57
else
141)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
106
else
7)
else
(if i.val < 534 then
58
else
68))
else
(if i.val < 537 then
(if i.val < 536 then
121
else
54)
else
(if i.val < 538 then
0
else
(if i.val < 539 then
0
else
0))))))))))
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
0)
else
(if i.val < 543 then
0
else
0))
else
(if i.val < 546 then
(if i.val < 545 then
0
else
27)
else
(if i.val < 547 then
0
else
0)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
0
else
0)
else
(if i.val < 551 then
0
else
0))
else
(if i.val < 554 then
(if i.val < 553 then
125
else
0)
else
(if i.val < 555 then
0
else
87))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
61
else
5)
else
(if i.val < 559 then
88
else
0))
else
(if i.val < 562 then
(if i.val < 561 then
26
else
127)
else
(if i.val < 563 then
127
else
0)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
121
else
65)
else
(if i.val < 567 then
94
else
0))
else
(if i.val < 570 then
(if i.val < 569 then
0
else
69)
else
(if i.val < 571 then
7
else
(if i.val < 572 then
0
else
0))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
87
else
127)
else
(if i.val < 576 then
56
else
26))
else
(if i.val < 579 then
(if i.val < 578 then
125
else
56)
else
(if i.val < 580 then
93
else
63)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
0
else
56)
else
(if i.val < 584 then
84
else
5))
else
(if i.val < 587 then
(if i.val < 586 then
7
else
93)
else
(if i.val < 588 then
87
else
(if i.val < 589 then
65
else
89)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
55
else
142)
else
(if i.val < 593 then
86
else
89))
else
(if i.val < 596 then
(if i.val < 595 then
87
else
5)
else
(if i.val < 597 then
9
else
7)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
115
else
87)
else
(if i.val < 601 then
127
else
23))
else
(if i.val < 604 then
(if i.val < 603 then
126
else
40)
else
(if i.val < 605 then
48
else
(if i.val < 606 then
11
else
136)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
80
else
87)
else
(if i.val < 610 then
47
else
11))
else
(if i.val < 613 then
(if i.val < 612 then
43
else
11)
else
(if i.val < 614 then
71
else
125)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
110
else
19)
else
(if i.val < 618 then
76
else
133))
else
(if i.val < 621 then
(if i.val < 620 then
27
else
62)
else
(if i.val < 622 then
0
else
(if i.val < 623 then
0
else
0)))))
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
(if i.val < 640 then
0
else
0))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
0
else
0)
else
(if i.val < 644 then
0
else
0))
else
(if i.val < 647 then
(if i.val < 646 then
0
else
0)
else
(if i.val < 648 then
0
else
0)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
0
else
0)
else
(if i.val < 652 then
0
else
0))
else
(if i.val < 655 then
(if i.val < 654 then
0
else
0)
else
(if i.val < 656 then
0
else
(if i.val < 657 then
0
else
0)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
0
else
0)
else
(if i.val < 661 then
0
else
0))
else
(if i.val < 664 then
(if i.val < 663 then
0
else
0)
else
(if i.val < 665 then
0
else
0)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
0
else
0)
else
(if i.val < 669 then
0
else
0))
else
(if i.val < 672 then
(if i.val < 671 then
0
else
0)
else
(if i.val < 673 then
0
else
(if i.val < 674 then
0
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
0
else
0)
else
(if i.val < 678 then
0
else
0))
else
(if i.val < 681 then
(if i.val < 680 then
0
else
0)
else
(if i.val < 682 then
0
else
0)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
0
else
0)
else
(if i.val < 686 then
88
else
0))
else
(if i.val < 689 then
(if i.val < 688 then
23
else
33)
else
(if i.val < 690 then
62
else
10))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
76
else
1)
else
(if i.val < 694 then
5
else
57))
else
(if i.val < 697 then
(if i.val < 696 then
84
else
84)
else
(if i.val < 698 then
19
else
33)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
107
else
107)
else
(if i.val < 702 then
7
else
115))
else
(if i.val < 705 then
(if i.val < 704 then
11
else
60)
else
(if i.val < 706 then
2
else
(if i.val < 707 then
37
else
84))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
2
else
7)
else
(if i.val < 711 then
68
else
48))
else
(if i.val < 714 then
(if i.val < 713 then
5
else
43)
else
(if i.val < 715 then
33
else
62)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
116
else
78)
else
(if i.val < 719 then
58
else
30))
else
(if i.val < 722 then
(if i.val < 721 then
2
else
127)
else
(if i.val < 723 then
34
else
(if i.val < 724 then
129
else
30)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
58
else
68)
else
(if i.val < 728 then
9
else
54))
else
(if i.val < 731 then
(if i.val < 730 then
0
else
0)
else
(if i.val < 732 then
5
else
0)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
0
else
7)
else
(if i.val < 736 then
108
else
7))
else
(if i.val < 739 then
(if i.val < 738 then
33
else
76)
else
(if i.val < 740 then
86
else
(if i.val < 741 then
48
else
11)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
48
else
0)
else
(if i.val < 745 then
48
else
40))
else
(if i.val < 748 then
(if i.val < 747 then
62
else
0)
else
(if i.val < 749 then
0
else
0)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
27
else
0)
else
(if i.val < 753 then
0
else
0))
else
(if i.val < 756 then
(if i.val < 755 then
0
else
55)
else
(if i.val < 757 then
25
else
(if i.val < 758 then
66
else
26)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
11
else
40)
else
(if i.val < 762 then
11
else
1))
else
(if i.val < 765 then
(if i.val < 764 then
10
else
21)
else
(if i.val < 766 then
40
else
73)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
58
else
11)
else
(if i.val < 770 then
72
else
68))
else
(if i.val < 773 then
(if i.val < 772 then
48
else
26)
else
(if i.val < 774 then
92
else
(if i.val < 775 then
32
else
141))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
106
else
58)
else
(if i.val < 779 then
121
else
54))
else
(if i.val < 782 then
(if i.val < 781 then
8
else
137)
else
(if i.val < 783 then
92
else
91)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
93
else
93)
else
(if i.val < 787 then
56
else
87))
else
(if i.val < 790 then
(if i.val < 789 then
21
else
73)
else
(if i.val < 791 then
141
else
(if i.val < 792 then
63
else
122)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
27
else
107)
else
(if i.val < 796 then
0
else
0))
else
(if i.val < 799 then
(if i.val < 798 then
0
else
0)
else
(if i.val < 800 then
0
else
88)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
0
else
0)
else
(if i.val < 804 then
0
else
60))
else
(if i.val < 807 then
(if i.val < 806 then
0
else
0)
else
(if i.val < 808 then
27
else
(if i.val < 809 then
0
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
0
else
0)
else
(if i.val < 813 then
0
else
0))
else
(if i.val < 816 then
(if i.val < 815 then
0
else
0)
else
(if i.val < 817 then
0
else
0)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
0
else
0)
else
(if i.val < 821 then
125
else
0))
else
(if i.val < 824 then
(if i.val < 823 then
87
else
27)
else
(if i.val < 825 then
0
else
26))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
127
else
0)
else
(if i.val < 829 then
121
else
61))
else
(if i.val < 832 then
(if i.val < 831 then
94
else
110)
else
(if i.val < 833 then
88
else
0)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
26
else
139)
else
(if i.val < 837 then
56
else
87))
else
(if i.val < 840 then
(if i.val < 839 then
11
else
56)
else
(if i.val < 841 then
55
else
(if i.val < 842 then
142
else
26))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
87
else
5)
else
(if i.val < 846 then
0
else
19))
else
(if i.val < 849 then
(if i.val < 848 then
127
else
84)
else
(if i.val < 850 then
40
else
11)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
136
else
33)
else
(if i.val < 854 then
47
else
26))
else
(if i.val < 857 then
(if i.val < 856 then
26
else
11)
else
(if i.val < 858 then
59
else
(if i.val < 859 then
142
else
58)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
84
else
23)
else
(if i.val < 863 then
107
else
62))
else
(if i.val < 866 then
(if i.val < 865 then
10
else
76)
else
(if i.val < 867 then
18
else
5)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
10
else
21)
else
(if i.val < 871 then
8
else
56))
else
(if i.val < 874 then
(if i.val < 873 then
73
else
5)
else
(if i.val < 875 then
107
else
(if i.val < 876 then
107
else
110)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
56
else
16)
else
(if i.val < 880 then
19
else
84))
else
(if i.val < 883 then
(if i.val < 882 then
84
else
127)
else
(if i.val < 884 then
72
else
68)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
11
else
5)
else
(if i.val < 888 then
86
else
136))
else
(if i.val < 891 then
(if i.val < 890 then
69
else
11)
else
(if i.val < 892 then
35
else
(if i.val < 893 then
68
else
134)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
68
else
11)
else
(if i.val < 897 then
11
else
106))
else
(if i.val < 900 then
(if i.val < 899 then
36
else
58)
else
(if i.val < 901 then
92
else
111)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
111
else
0)
else
(if i.val < 905 then
0
else
0))
else
(if i.val < 908 then
(if i.val < 907 then
0
else
0)
else
(if i.val < 909 then
0
else
(if i.val < 910 then
0
else
0))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
0
else
0)
else
(if i.val < 914 then
0
else
0))
else
(if i.val < 917 then
(if i.val < 916 then
0
else
0)
else
(if i.val < 918 then
0
else
0)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
0
else
0)
else
(if i.val < 922 then
0
else
0))
else
(if i.val < 925 then
(if i.val < 924 then
0
else
0)
else
(if i.val < 926 then
0
else
(if i.val < 927 then
0
else
0)))))
else
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
(if i.val < 944 then
0
else
0))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
0
else
0)
else
(if i.val < 948 then
0
else
0))
else
(if i.val < 951 then
(if i.val < 950 then
0
else
0)
else
(if i.val < 952 then
0
else
0)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
0
else
80)
else
(if i.val < 956 then
137
else
92))
else
(if i.val < 959 then
(if i.val < 958 then
91
else
136)
else
(if i.val < 960 then
93
else
2))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
112
else
36)
else
(if i.val < 964 then
37
else
133))
else
(if i.val < 967 then
(if i.val < 966 then
127
else
7)
else
(if i.val < 968 then
0
else
107)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
0
else
0)
else
(if i.val < 972 then
115
else
62))
else
(if i.val < 975 then
(if i.val < 974 then
48
else
9)
else
(if i.val < 976 then
54
else
(if i.val < 977 then
93
else
141))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
117
else
47)
else
(if i.val < 981 then
48
else
48))
else
(if i.val < 984 then
(if i.val < 983 then
0
else
27)
else
(if i.val < 985 then
0
else
0)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
0
else
0)
else
(if i.val < 989 then
0
else
7))
else
(if i.val < 992 then
(if i.val < 991 then
0
else
33)
else
(if i.val < 993 then
33
else
(if i.val < 994 then
27
else
0)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
48
else
0)
else
(if i.val < 998 then
48
else
0))
else
(if i.val < 1001 then
(if i.val < 1000 then
48
else
0)
else
(if i.val < 1002 then
62
else
0)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
127
else
121)
else
(if i.val < 1006 then
27
else
88))
else
(if i.val < 1009 then
(if i.val < 1008 then
0
else
26)
else
(if i.val < 1010 then
56
else
(if i.val < 1011 then
55
else
25)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
138
else
57)
else
(if i.val < 1015 then
19
else
69))
else
(if i.val < 1018 then
(if i.val < 1017 then
11
else
1)
else
(if i.val < 1019 then
26
else
94)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
33
else
73)
else
(if i.val < 1023 then
102
else
26))
else
(if i.val < 1026 then
(if i.val < 1025 then
72
else
28)
else
(if i.val < 1027 then
90
else
(if i.val < 1028 then
26
else
106)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
56
else
141)
else
(if i.val < 1032 then
0
else
136))
else
(if i.val < 1035 then
(if i.val < 1034 then
121
else
71)
else
(if i.val < 1036 then
70
else
137)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
37
else
107)
else
(if i.val < 1040 then
93
else
128))
else
(if i.val < 1043 then
(if i.val < 1042 then
56
else
112)
else
(if i.val < 1044 then
35
else
(if i.val < 1045 then
138
else
26))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
63
else
142)
else
(if i.val < 1049 then
27
else
76))
else
(if i.val < 1052 then
(if i.val < 1051 then
0
else
0)
else
(if i.val < 1053 then
0
else
0)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
0
else
0)
else
(if i.val < 1057 then
0
else
0))
else
(if i.val < 1060 then
(if i.val < 1059 then
0
else
117)
else
(if i.val < 1061 then
29
else
(if i.val < 1062 then
2
else
16)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
133
else
27)
else
(if i.val < 1066 then
0
else
0))
else
(if i.val < 1069 then
(if i.val < 1068 then
93
else
0)
else
(if i.val < 1070 then
0
else
0)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
0
else
61)
else
(if i.val < 1074 then
127
else
107))
else
(if i.val < 1077 then
(if i.val < 1076 then
29
else
68)
else
(if i.val < 1078 then
124
else
(if i.val < 1079 then
0
else
106)))))))))))

def g32p_row06_cosetBranchFactorColumn2 : Fin 1080 → Fin 144 :=
  fun i => (if i.val < 540 then
(if i.val < 270 then
(if i.val < 135 then
(if i.val < 67 then
(if i.val < 33 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
79
else
92)
else
(if i.val < 3 then
45
else
97))
else
(if i.val < 6 then
(if i.val < 5 then
112
else
26)
else
(if i.val < 7 then
12
else
54)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
41
else
6)
else
(if i.val < 11 then
46
else
132))
else
(if i.val < 14 then
(if i.val < 13 then
87
else
10)
else
(if i.val < 15 then
73
else
112))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
56
else
32)
else
(if i.val < 19 then
37
else
101))
else
(if i.val < 22 then
(if i.val < 21 then
121
else
90)
else
(if i.val < 23 then
111
else
27)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
42
else
111)
else
(if i.val < 27 then
12
else
54))
else
(if i.val < 30 then
(if i.val < 29 then
85
else
11)
else
(if i.val < 31 then
82
else
(if i.val < 32 then
20
else
113))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
24
else
118)
else
(if i.val < 36 then
98
else
129))
else
(if i.val < 39 then
(if i.val < 38 then
28
else
46)
else
(if i.val < 40 then
130
else
117)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
85
else
137)
else
(if i.val < 44 then
137
else
99))
else
(if i.val < 47 then
(if i.val < 46 then
124
else
73)
else
(if i.val < 48 then
12
else
(if i.val < 49 then
37
else
112)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
2
else
65)
else
(if i.val < 53 then
59
else
138))
else
(if i.val < 56 then
(if i.val < 55 then
94
else
123)
else
(if i.val < 57 then
81
else
89)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
38
else
47)
else
(if i.val < 61 then
131
else
141))
else
(if i.val < 64 then
(if i.val < 63 then
114
else
135)
else
(if i.val < 65 then
70
else
(if i.val < 66 then
111
else
123)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
90
else
23)
else
(if i.val < 70 then
1
else
47))
else
(if i.val < 73 then
(if i.val < 72 then
123
else
42)
else
(if i.val < 74 then
91
else
111)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
62
else
141)
else
(if i.val < 78 then
71
else
62))
else
(if i.val < 81 then
(if i.val < 80 then
48
else
89)
else
(if i.val < 82 then
82
else
(if i.val < 83 then
11
else
60)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
21
else
117)
else
(if i.val < 87 then
113
else
114))
else
(if i.val < 90 then
(if i.val < 89 then
89
else
121)
else
(if i.val < 91 then
14
else
112)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
116
else
24)
else
(if i.val < 95 then
45
else
136))
else
(if i.val < 98 then
(if i.val < 97 then
95
else
95)
else
(if i.val < 99 then
107
else
(if i.val < 100 then
121
else
9))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
60
else
79)
else
(if i.val < 104 then
71
else
122))
else
(if i.val < 107 then
(if i.val < 106 then
137
else
117)
else
(if i.val < 108 then
23
else
37)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
92
else
85)
else
(if i.val < 112 then
90
else
116))
else
(if i.val < 115 then
(if i.val < 114 then
66
else
99)
else
(if i.val < 116 then
99
else
(if i.val < 117 then
70
else
110)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
41
else
116)
else
(if i.val < 121 then
94
else
70))
else
(if i.val < 124 then
(if i.val < 123 then
133
else
70)
else
(if i.val < 125 then
12
else
65)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
63
else
122)
else
(if i.val < 129 then
65
else
57))
else
(if i.val < 132 then
(if i.val < 131 then
90
else
87)
else
(if i.val < 133 then
69
else
(if i.val < 134 then
4
else
110))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
137
else
78)
else
(if i.val < 138 then
94
else
36))
else
(if i.val < 141 then
(if i.val < 140 then
89
else
124)
else
(if i.val < 142 then
5
else
81)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
81
else
27)
else
(if i.val < 146 then
132
else
48))
else
(if i.val < 149 then
(if i.val < 148 then
38
else
16)
else
(if i.val < 150 then
70
else
36))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
134
else
115)
else
(if i.val < 154 then
119
else
53))
else
(if i.val < 157 then
(if i.val < 156 then
113
else
115)
else
(if i.val < 158 then
3
else
5)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
102
else
17)
else
(if i.val < 162 then
29
else
130))
else
(if i.val < 165 then
(if i.val < 164 then
111
else
123)
else
(if i.val < 166 then
14
else
(if i.val < 167 then
135
else
46))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
37
else
74)
else
(if i.val < 171 then
90
else
48))
else
(if i.val < 174 then
(if i.val < 173 then
62
else
29)
else
(if i.val < 175 then
16
else
94)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
91
else
42)
else
(if i.val < 179 then
42
else
30))
else
(if i.val < 182 then
(if i.val < 181 then
29
else
137)
else
(if i.val < 183 then
29
else
(if i.val < 184 then
82
else
28)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
102
else
56)
else
(if i.val < 188 then
122
else
47))
else
(if i.val < 191 then
(if i.val < 190 then
62
else
68)
else
(if i.val < 192 then
119
else
73)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
135
else
135)
else
(if i.val < 196 then
68
else
17))
else
(if i.val < 199 then
(if i.val < 198 then
51
else
21)
else
(if i.val < 200 then
96
else
(if i.val < 201 then
118
else
80)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
21
else
138)
else
(if i.val < 205 then
62
else
102))
else
(if i.val < 208 then
(if i.val < 207 then
21
else
22)
else
(if i.val < 209 then
44
else
2)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
77
else
34)
else
(if i.val < 213 then
73
else
45))
else
(if i.val < 216 then
(if i.val < 215 then
37
else
130)
else
(if i.val < 217 then
123
else
(if i.val < 218 then
135
else
13)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
116
else
45)
else
(if i.val < 222 then
60
else
132))
else
(if i.val < 225 then
(if i.val < 224 then
85
else
44)
else
(if i.val < 226 then
108
else
136)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
95
else
98)
else
(if i.val < 230 then
6
else
41))
else
(if i.val < 233 then
(if i.val < 232 then
91
else
5)
else
(if i.val < 234 then
70
else
(if i.val < 235 then
37
else
94))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
41
else
37)
else
(if i.val < 239 then
82
else
117))
else
(if i.val < 242 then
(if i.val < 241 then
120
else
10)
else
(if i.val < 243 then
79
else
120)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
85
else
13)
else
(if i.val < 247 then
117
else
117))
else
(if i.val < 250 then
(if i.val < 249 then
110
else
45)
else
(if i.val < 251 then
88
else
(if i.val < 252 then
110
else
110)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
132
else
41)
else
(if i.val < 256 then
69
else
44))
else
(if i.val < 259 then
(if i.val < 258 then
130
else
121)
else
(if i.val < 260 then
90
else
79)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
121
else
66)
else
(if i.val < 264 then
121
else
59))
else
(if i.val < 267 then
(if i.val < 266 then
90
else
23)
else
(if i.val < 268 then
79
else
(if i.val < 269 then
131
else
67)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
116
else
43)
else
(if i.val < 273 then
94
else
130))
else
(if i.val < 276 then
(if i.val < 275 then
65
else
28)
else
(if i.val < 277 then
117
else
53)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
78
else
76)
else
(if i.val < 281 then
94
else
56))
else
(if i.val < 284 then
(if i.val < 283 then
78
else
132)
else
(if i.val < 285 then
141
else
88))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
86
else
65)
else
(if i.val < 289 then
65
else
87))
else
(if i.val < 292 then
(if i.val < 291 then
110
else
127)
else
(if i.val < 293 then
132
else
12)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
78
else
109)
else
(if i.val < 297 then
54
else
25))
else
(if i.val < 300 then
(if i.val < 299 then
89
else
30)
else
(if i.val < 301 then
5
else
(if i.val < 302 then
142
else
137))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
10
else
106)
else
(if i.val < 306 then
47
else
72))
else
(if i.val < 309 then
(if i.val < 308 then
10
else
139)
else
(if i.val < 310 then
125
else
33)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
21
else
27)
else
(if i.val < 314 then
38
else
115))
else
(if i.val < 317 then
(if i.val < 316 then
5
else
34)
else
(if i.val < 318 then
70
else
(if i.val < 319 then
30
else
124)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
8
else
93)
else
(if i.val < 323 then
93
else
38))
else
(if i.val < 326 then
(if i.val < 325 then
46
else
70)
else
(if i.val < 327 then
61
else
80)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
31
else
134)
else
(if i.val < 331 then
121
else
10))
else
(if i.val < 334 then
(if i.val < 333 then
53
else
17)
else
(if i.val < 335 then
70
else
(if i.val < 336 then
30
else
12)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
35
else
69)
else
(if i.val < 340 then
2
else
131))
else
(if i.val < 343 then
(if i.val < 342 then
8
else
59)
else
(if i.val < 344 then
132
else
65)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
45
else
107)
else
(if i.val < 348 then
12
else
130))
else
(if i.val < 351 then
(if i.val < 350 then
111
else
85)
else
(if i.val < 352 then
32
else
(if i.val < 353 then
39
else
14)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
12
else
16)
else
(if i.val < 357 then
77
else
141))
else
(if i.val < 360 then
(if i.val < 359 then
14
else
63)
else
(if i.val < 361 then
7
else
119)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
16
else
12)
else
(if i.val < 365 then
66
else
7))
else
(if i.val < 368 then
(if i.val < 367 then
58
else
60)
else
(if i.val < 369 then
69
else
(if i.val < 370 then
92
else
122))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
35
else
56)
else
(if i.val < 374 then
94
else
119))
else
(if i.val < 377 then
(if i.val < 376 then
115
else
127)
else
(if i.val < 378 then
42
else
91)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
68
else
91)
else
(if i.val < 382 then
91
else
16))
else
(if i.val < 385 then
(if i.val < 384 then
42
else
42)
else
(if i.val < 386 then
14
else
(if i.val < 387 then
29
else
69)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
29
else
90)
else
(if i.val < 391 then
83
else
116))
else
(if i.val < 394 then
(if i.val < 393 then
111
else
119)
else
(if i.val < 395 then
102
else
102)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
38
else
62)
else
(if i.val < 399 then
136
else
62))
else
(if i.val < 402 then
(if i.val < 401 then
94
else
15)
else
(if i.val < 403 then
32
else
(if i.val < 404 then
135
else
23))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
73
else
135)
else
(if i.val < 408 then
140
else
21))
else
(if i.val < 411 then
(if i.val < 410 then
12
else
62)
else
(if i.val < 412 then
79
else
96)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
28
else
122)
else
(if i.val < 416 then
141
else
134))
else
(if i.val < 419 then
(if i.val < 418 then
142
else
112)
else
(if i.val < 420 then
5
else
102))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
21
else
21)
else
(if i.val < 424 then
62
else
120))
else
(if i.val < 427 then
(if i.val < 426 then
14
else
11)
else
(if i.val < 428 then
62
else
119)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
9
else
126)
else
(if i.val < 432 then
5
else
97))
else
(if i.val < 435 then
(if i.val < 434 then
28
else
123)
else
(if i.val < 436 then
31
else
(if i.val < 437 then
107
else
110))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
135
else
109)
else
(if i.val < 441 then
101
else
21))
else
(if i.val < 444 then
(if i.val < 443 then
135
else
46)
else
(if i.val < 445 then
123
else
6)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
15
else
135)
else
(if i.val < 449 then
85
else
46))
else
(if i.val < 452 then
(if i.val < 451 then
96
else
24)
else
(if i.val < 453 then
45
else
(if i.val < 454 then
46
else
66)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
95
else
95)
else
(if i.val < 458 then
96
else
46))
else
(if i.val < 461 then
(if i.val < 460 then
37
else
95)
else
(if i.val < 462 then
20
else
78)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
41
else
5)
else
(if i.val < 466 then
20
else
94))
else
(if i.val < 469 then
(if i.val < 468 then
110
else
88)
else
(if i.val < 470 then
60
else
(if i.val < 471 then
72
else
95)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
65
else
37)
else
(if i.val < 475 then
117
else
60))
else
(if i.val < 478 then
(if i.val < 477 then
117
else
20)
else
(if i.val < 479 then
67
else
120)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
109
else
10)
else
(if i.val < 483 then
85
else
132))
else
(if i.val < 486 then
(if i.val < 485 then
13
else
11)
else
(if i.val < 487 then
61
else
(if i.val < 488 then
94
else
110)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
137
else
41)
else
(if i.val < 492 then
127
else
41))
else
(if i.val < 495 then
(if i.val < 494 then
121
else
37)
else
(if i.val < 496 then
85
else
121)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
59
else
112)
else
(if i.val < 500 then
94
else
110))
else
(if i.val < 503 then
(if i.val < 502 then
28
else
132)
else
(if i.val < 504 then
41
else
(if i.val < 505 then
130
else
111))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
12
else
31)
else
(if i.val < 509 then
117
else
121))
else
(if i.val < 512 then
(if i.val < 511 then
130
else
73)
else
(if i.val < 513 then
28
else
43)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
65
else
60)
else
(if i.val < 517 then
117
else
10))
else
(if i.val < 520 then
(if i.val < 519 then
112
else
41)
else
(if i.val < 521 then
65
else
(if i.val < 522 then
63
else
68)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
1
else
26)
else
(if i.val < 526 then
102
else
69))
else
(if i.val < 529 then
(if i.val < 528 then
34
else
26)
else
(if i.val < 530 then
11
else
86)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
87
else
10)
else
(if i.val < 534 then
74
else
132))
else
(if i.val < 537 then
(if i.val < 536 then
90
else
44)
else
(if i.val < 538 then
42
else
(if i.val < 539 then
131
else
118))))))))))
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
141
else
32)
else
(if i.val < 543 then
89
else
43))
else
(if i.val < 546 then
(if i.val < 545 then
23
else
139)
else
(if i.val < 547 then
101
else
35)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
14
else
124)
else
(if i.val < 551 then
137
else
45))
else
(if i.val < 554 then
(if i.val < 553 then
58
else
32)
else
(if i.val < 555 then
98
else
50))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
90
else
39)
else
(if i.val < 559 then
22
else
93))
else
(if i.val < 562 then
(if i.val < 561 then
121
else
79)
else
(if i.val < 563 then
105
else
8)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
124
else
33)
else
(if i.val < 567 then
71
else
57))
else
(if i.val < 570 then
(if i.val < 569 then
50
else
64)
else
(if i.val < 571 then
132
else
(if i.val < 572 then
101
else
19))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
33
else
137)
else
(if i.val < 576 then
142
else
128))
else
(if i.val < 579 then
(if i.val < 578 then
141
else
92)
else
(if i.val < 580 then
139
else
59)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
70
else
129)
else
(if i.val < 584 then
63
else
38))
else
(if i.val < 587 then
(if i.val < 586 then
38
else
63)
else
(if i.val < 588 then
51
else
(if i.val < 589 then
106
else
93)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
99
else
131)
else
(if i.val < 593 then
121
else
45))
else
(if i.val < 596 then
(if i.val < 595 then
71
else
124)
else
(if i.val < 597 then
101
else
38)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
80
else
97)
else
(if i.val < 601 then
101
else
134))
else
(if i.val < 604 then
(if i.val < 603 then
84
else
12)
else
(if i.val < 605 then
100
else
(if i.val < 606 then
105
else
49)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
70
else
124)
else
(if i.val < 610 then
139
else
109))
else
(if i.val < 613 then
(if i.val < 612 then
115
else
126)
else
(if i.val < 614 then
135
else
53)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
8
else
5)
else
(if i.val < 618 then
53
else
53))
else
(if i.val < 621 then
(if i.val < 620 then
141
else
17)
else
(if i.val < 622 then
29
else
(if i.val < 623 then
29
else
4)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
111
else
12)
else
(if i.val < 627 then
104
else
133))
else
(if i.val < 630 then
(if i.val < 629 then
14
else
42)
else
(if i.val < 631 then
97
else
140)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
14
else
30)
else
(if i.val < 635 then
49
else
106))
else
(if i.val < 638 then
(if i.val < 637 then
77
else
9)
else
(if i.val < 639 then
16
else
(if i.val < 640 then
77
else
133))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
96
else
63)
else
(if i.val < 644 then
63
else
12))
else
(if i.val < 647 then
(if i.val < 646 then
142
else
95)
else
(if i.val < 648 then
47
else
40)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
143
else
119)
else
(if i.val < 652 then
77
else
91))
else
(if i.val < 655 then
(if i.val < 654 then
80
else
78)
else
(if i.val < 656 then
63
else
(if i.val < 657 then
66
else
136)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
12
else
68)
else
(if i.val < 661 then
86
else
7))
else
(if i.val < 664 then
(if i.val < 663 then
36
else
89)
else
(if i.val < 665 then
82
else
114)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
14
else
72)
else
(if i.val < 669 then
91
else
2))
else
(if i.val < 672 then
(if i.val < 671 then
119
else
42)
else
(if i.val < 673 then
40
else
(if i.val < 674 then
71
else
62))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
104
else
95)
else
(if i.val < 678 then
4
else
91))
else
(if i.val < 681 then
(if i.val < 680 then
133
else
42)
else
(if i.val < 682 then
11
else
37)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
82
else
11)
else
(if i.val < 686 then
12
else
60))
else
(if i.val < 689 then
(if i.val < 688 then
141
else
119)
else
(if i.val < 690 then
33
else
30))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
38
else
52)
else
(if i.val < 694 then
119
else
42))
else
(if i.val < 697 then
(if i.val < 696 then
119
else
141)
else
(if i.val < 698 then
32
else
63)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
73
else
134)
else
(if i.val < 702 then
123
else
89))
else
(if i.val < 705 then
(if i.val < 704 then
47
else
47)
else
(if i.val < 706 then
135
else
(if i.val < 707 then
135
else
73))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
73
else
28)
else
(if i.val < 711 then
138
else
119))
else
(if i.val < 714 then
(if i.val < 713 then
21
else
92)
else
(if i.val < 715 then
42
else
39)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
22
else
138)
else
(if i.val < 719 then
20
else
138))
else
(if i.val < 722 then
(if i.val < 721 then
66
else
92)
else
(if i.val < 723 then
62
else
(if i.val < 724 then
62
else
120)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
112
else
21)
else
(if i.val < 728 then
112
else
51))
else
(if i.val < 731 then
(if i.val < 730 then
75
else
73)
else
(if i.val < 732 then
47
else
5)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
31
else
28)
else
(if i.val < 736 then
43
else
122))
else
(if i.val < 739 then
(if i.val < 738 then
140
else
101)
else
(if i.val < 740 then
6
else
(if i.val < 741 then
77
else
116)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
6
else
6)
else
(if i.val < 745 then
46
else
24))
else
(if i.val < 748 then
(if i.val < 747 then
99
else
66)
else
(if i.val < 749 then
72
else
75)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
42
else
95)
else
(if i.val < 753 then
6
else
94))
else
(if i.val < 756 then
(if i.val < 755 then
72
else
5)
else
(if i.val < 757 then
79
else
(if i.val < 758 then
29
else
5)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
86
else
65)
else
(if i.val < 762 then
135
else
37))
else
(if i.val < 765 then
(if i.val < 764 then
60
else
121)
else
(if i.val < 766 then
86
else
41)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
117
else
37)
else
(if i.val < 770 then
13
else
130))
else
(if i.val < 773 then
(if i.val < 772 then
117
else
9)
else
(if i.val < 774 then
110
else
(if i.val < 775 then
110
else
26))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
88
else
93)
else
(if i.val < 779 then
45
else
140))
else
(if i.val < 782 then
(if i.val < 781 then
70
else
108)
else
(if i.val < 783 then
122
else
94)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
10
else
8)
else
(if i.val < 787 then
131
else
52))
else
(if i.val < 790 then
(if i.val < 789 then
70
else
36)
else
(if i.val < 791 then
61
else
(if i.val < 792 then
58
else
55)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
79
else
65)
else
(if i.val < 796 then
39
else
54))
else
(if i.val < 799 then
(if i.val < 798 then
19
else
48)
else
(if i.val < 800 then
89
else
12)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
6
else
15)
else
(if i.val < 804 then
12
else
43))
else
(if i.val < 807 then
(if i.val < 806 then
30
else
12)
else
(if i.val < 808 then
65
else
(if i.val < 809 then
59
else
86)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
28
else
122)
else
(if i.val < 813 then
19
else
133))
else
(if i.val < 816 then
(if i.val < 815 then
124
else
134)
else
(if i.val < 817 then
30
else
124)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
101
else
12)
else
(if i.val < 821 then
98
else
33))
else
(if i.val < 824 then
(if i.val < 823 then
10
else
129)
else
(if i.val < 825 then
98
else
80))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
100
else
137)
else
(if i.val < 829 then
81
else
51))
else
(if i.val < 832 then
(if i.val < 831 then
61
else
34)
else
(if i.val < 833 then
30
else
83)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
128
else
139)
else
(if i.val < 837 then
3
else
77))
else
(if i.val < 840 then
(if i.val < 839 then
3
else
8)
else
(if i.val < 841 then
73
else
(if i.val < 842 then
52
else
19))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
64
else
64)
else
(if i.val < 846 then
64
else
25))
else
(if i.val < 849 then
(if i.val < 848 then
137
else
80)
else
(if i.val < 850 then
19
else
101)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
69
else
19)
else
(if i.val < 854 then
78
else
128))
else
(if i.val < 857 then
(if i.val < 856 then
56
else
137)
else
(if i.val < 858 then
53
else
(if i.val < 859 then
23
else
38)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
143
else
124)
else
(if i.val < 863 then
18
else
59))
else
(if i.val < 866 then
(if i.val < 865 then
141
else
8)
else
(if i.val < 867 then
134
else
75)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
143
else
18)
else
(if i.val < 871 then
70
else
70))
else
(if i.val < 874 then
(if i.val < 873 then
28
else
32)
else
(if i.val < 875 then
31
else
(if i.val < 876 then
67
else
28)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
12
else
77)
else
(if i.val < 880 then
32
else
8))
else
(if i.val < 883 then
(if i.val < 882 then
80
else
73)
else
(if i.val < 884 then
105
else
118)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
49
else
101)
else
(if i.val < 888 then
96
else
103))
else
(if i.val < 891 then
(if i.val < 890 then
31
else
35)
else
(if i.val < 892 then
113
else
(if i.val < 893 then
30
else
35)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
35
else
120)
else
(if i.val < 897 then
58
else
8))
else
(if i.val < 900 then
(if i.val < 899 then
57
else
23)
else
(if i.val < 901 then
80
else
17)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
99
else
60)
else
(if i.val < 905 then
25
else
123))
else
(if i.val < 908 then
(if i.val < 907 then
107
else
130)
else
(if i.val < 909 then
133
else
(if i.val < 910 then
133
else
85))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
78
else
14)
else
(if i.val < 914 then
75
else
118))
else
(if i.val < 917 then
(if i.val < 916 then
16
else
111)
else
(if i.val < 918 then
133
else
100)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
111
else
133)
else
(if i.val < 922 then
43
else
52))
else
(if i.val < 925 then
(if i.val < 924 then
100
else
143)
else
(if i.val < 926 then
54
else
(if i.val < 927 then
103
else
12)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
91
else
2)
else
(if i.val < 931 then
11
else
68))
else
(if i.val < 934 then
(if i.val < 933 then
68
else
60)
else
(if i.val < 935 then
66
else
91)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
12
else
2)
else
(if i.val < 939 then
23
else
16))
else
(if i.val < 942 then
(if i.val < 941 then
66
else
48)
else
(if i.val < 943 then
7
else
(if i.val < 944 then
12
else
91))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
4
else
42)
else
(if i.val < 948 then
42
else
63))
else
(if i.val < 951 then
(if i.val < 950 then
51
else
60)
else
(if i.val < 952 then
130
else
46)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
114
else
66)
else
(if i.val < 956 then
40
else
136))
else
(if i.val < 959 then
(if i.val < 958 then
122
else
68)
else
(if i.val < 960 then
94
else
40))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
124
else
122)
else
(if i.val < 964 then
99
else
90))
else
(if i.val < 967 then
(if i.val < 966 then
55
else
115)
else
(if i.val < 968 then
15
else
14)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
9
else
126)
else
(if i.val < 972 then
13
else
110))
else
(if i.val < 975 then
(if i.val < 974 then
14
else
117)
else
(if i.val < 976 then
137
else
(if i.val < 977 then
5
else
139))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
99
else
131)
else
(if i.val < 981 then
90
else
32))
else
(if i.val < 984 then
(if i.val < 983 then
125
else
69)
else
(if i.val < 985 then
76
else
75)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
54
else
48)
else
(if i.val < 989 then
38
else
100))
else
(if i.val < 992 then
(if i.val < 991 then
73
else
26)
else
(if i.val < 993 then
89
else
(if i.val < 994 then
12
else
16)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
54
else
137)
else
(if i.val < 998 then
30
else
76))
else
(if i.val < 1001 then
(if i.val < 1000 then
86
else
47)
else
(if i.val < 1002 then
118
else
5)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
120
else
54)
else
(if i.val < 1006 then
12
else
67))
else
(if i.val < 1009 then
(if i.val < 1008 then
5
else
134)
else
(if i.val < 1010 then
19
else
(if i.val < 1011 then
64
else
51)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
110
else
57)
else
(if i.val < 1015 then
7
else
69))
else
(if i.val < 1018 then
(if i.val < 1017 then
71
else
73)
else
(if i.val < 1019 then
48
else
8)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
33
else
43)
else
(if i.val < 1023 then
109
else
40))
else
(if i.val < 1026 then
(if i.val < 1025 then
73
else
19)
else
(if i.val < 1027 then
69
else
(if i.val < 1028 then
142
else
128)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
116
else
74)
else
(if i.val < 1032 then
16
else
25))
else
(if i.val < 1035 then
(if i.val < 1034 then
106
else
70)
else
(if i.val < 1036 then
70
else
33)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
129
else
3)
else
(if i.val < 1040 then
83
else
23))
else
(if i.val < 1043 then
(if i.val < 1042 then
115
else
131)
else
(if i.val < 1044 then
118
else
(if i.val < 1045 then
106
else
84))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
5
else
35)
else
(if i.val < 1049 then
125
else
14))
else
(if i.val < 1052 then
(if i.val < 1051 then
29
else
89)
else
(if i.val < 1053 then
126
else
42)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
30
else
133)
else
(if i.val < 1057 then
139
else
56))
else
(if i.val < 1060 then
(if i.val < 1059 then
60
else
33)
else
(if i.val < 1061 then
141
else
(if i.val < 1062 then
114
else
133)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
102
else
37)
else
(if i.val < 1066 then
39
else
75))
else
(if i.val < 1069 then
(if i.val < 1068 then
89
else
47)
else
(if i.val < 1070 then
118
else
32)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
53
else
23)
else
(if i.val < 1074 then
16
else
22))
else
(if i.val < 1077 then
(if i.val < 1076 then
38
else
56)
else
(if i.val < 1078 then
100
else
(if i.val < 1079 then
2
else
112)))))))))))

def g32p_row06_cosetBranchFactor : Fin 3 → Fin 1080 → Fin 144 :=
  ![g32p_row06_cosetBranchFactorColumn0, g32p_row06_cosetBranchFactorColumn1, g32p_row06_cosetBranchFactorColumn2]

def g32p_row06_cosetLabels0 : Fin 1080 → Fin 360 :=
  fun i => (if i.val < 540 then
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
1)
else
(if i.val < 3 then
2
else
3))
else
(if i.val < 6 then
(if i.val < 5 then
4
else
5)
else
(if i.val < 7 then
6
else
7)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
8
else
9)
else
(if i.val < 11 then
10
else
11))
else
(if i.val < 14 then
(if i.val < 13 then
12
else
13)
else
(if i.val < 15 then
14
else
15))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
16
else
17)
else
(if i.val < 19 then
18
else
19))
else
(if i.val < 22 then
(if i.val < 21 then
20
else
21)
else
(if i.val < 23 then
22
else
23)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
24
else
25)
else
(if i.val < 27 then
26
else
27))
else
(if i.val < 30 then
(if i.val < 29 then
28
else
1)
else
(if i.val < 31 then
29
else
(if i.val < 32 then
30
else
31))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
32
else
33)
else
(if i.val < 36 then
34
else
35))
else
(if i.val < 39 then
(if i.val < 38 then
36
else
37)
else
(if i.val < 40 then
38
else
39)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
40
else
41)
else
(if i.val < 44 then
42
else
43))
else
(if i.val < 47 then
(if i.val < 46 then
44
else
45)
else
(if i.val < 48 then
46
else
(if i.val < 49 then
47
else
48)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
49
else
50)
else
(if i.val < 53 then
51
else
52))
else
(if i.val < 56 then
(if i.val < 55 then
53
else
54)
else
(if i.val < 57 then
55
else
6)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
56
else
57)
else
(if i.val < 61 then
58
else
59))
else
(if i.val < 64 then
(if i.val < 63 then
60
else
61)
else
(if i.val < 65 then
62
else
(if i.val < 66 then
63
else
64)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
65
else
66)
else
(if i.val < 70 then
67
else
68))
else
(if i.val < 73 then
(if i.val < 72 then
69
else
70)
else
(if i.val < 74 then
71
else
72)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
73
else
74)
else
(if i.val < 78 then
75
else
76))
else
(if i.val < 81 then
(if i.val < 80 then
77
else
7)
else
(if i.val < 82 then
36
else
(if i.val < 83 then
78
else
45)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
29
else
79)
else
(if i.val < 87 then
80
else
81))
else
(if i.val < 90 then
(if i.val < 89 then
82
else
83)
else
(if i.val < 91 then
84
else
85)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
9
else
86)
else
(if i.val < 95 then
87
else
88))
else
(if i.val < 98 then
(if i.val < 97 then
89
else
90)
else
(if i.val < 99 then
91
else
(if i.val < 100 then
92
else
93))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
94
else
95)
else
(if i.val < 104 then
96
else
97))
else
(if i.val < 107 then
(if i.val < 106 then
98
else
44)
else
(if i.val < 108 then
99
else
100)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
101
else
102)
else
(if i.val < 112 then
103
else
104))
else
(if i.val < 115 then
(if i.val < 114 then
105
else
106)
else
(if i.val < 116 then
107
else
(if i.val < 117 then
12
else
108)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
109
else
110)
else
(if i.val < 121 then
40
else
111))
else
(if i.val < 124 then
(if i.val < 123 then
112
else
113)
else
(if i.val < 125 then
114
else
115)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
116
else
52)
else
(if i.val < 129 then
117
else
118))
else
(if i.val < 132 then
(if i.val < 131 then
119
else
120)
else
(if i.val < 133 then
121
else
(if i.val < 134 then
122
else
123))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
124
else
125)
else
(if i.val < 138 then
126
else
127))
else
(if i.val < 141 then
(if i.val < 140 then
128
else
129)
else
(if i.val < 142 then
130
else
59)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
131
else
26)
else
(if i.val < 146 then
80
else
74))
else
(if i.val < 149 then
(if i.val < 148 then
33
else
132)
else
(if i.val < 150 then
133
else
134))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
135
else
85)
else
(if i.val < 154 then
136
else
137))
else
(if i.val < 157 then
(if i.val < 156 then
119
else
106)
else
(if i.val < 158 then
138
else
139)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
70
else
140)
else
(if i.val < 162 then
141
else
142))
else
(if i.val < 165 then
(if i.val < 164 then
143
else
49)
else
(if i.val < 166 then
144
else
(if i.val < 167 then
145
else
21))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
146
else
147)
else
(if i.val < 171 then
148
else
58))
else
(if i.val < 174 then
(if i.val < 173 then
149
else
68)
else
(if i.val < 175 then
150
else
151)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
152
else
153)
else
(if i.val < 179 then
110
else
118))
else
(if i.val < 182 then
(if i.val < 181 then
102
else
79)
else
(if i.val < 183 then
154
else
(if i.val < 184 then
155
else
156)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
25
else
157)
else
(if i.val < 188 then
158
else
126))
else
(if i.val < 191 then
(if i.val < 190 then
159
else
122)
else
(if i.val < 192 then
160
else
161)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
65
else
27)
else
(if i.val < 196 then
107
else
162))
else
(if i.val < 199 then
(if i.val < 198 then
4
else
36)
else
(if i.val < 200 then
163
else
(if i.val < 201 then
38
else
164)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
165
else
166)
else
(if i.val < 205 then
23
else
167))
else
(if i.val < 208 then
(if i.val < 207 then
29
else
100)
else
(if i.val < 209 then
95
else
168)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
41
else
22)
else
(if i.val < 213 then
169
else
30))
else
(if i.val < 216 then
(if i.val < 215 then
170
else
103)
else
(if i.val < 217 then
171
else
(if i.val < 218 then
76
else
172)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
32
else
173)
else
(if i.val < 222 then
97
else
86))
else
(if i.val < 225 then
(if i.val < 224 then
174
else
175)
else
(if i.val < 226 then
176
else
34)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
46
else
60)
else
(if i.val < 230 then
177
else
48))
else
(if i.val < 233 then
(if i.val < 232 then
111
else
178)
else
(if i.val < 234 then
96
else
(if i.val < 235 then
69
else
179))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
115
else
180)
else
(if i.val < 239 then
181
else
182))
else
(if i.val < 242 then
(if i.val < 241 then
183
else
184)
else
(if i.val < 243 then
185
else
92)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
45
else
186)
else
(if i.val < 247 then
187
else
188))
else
(if i.val < 250 then
(if i.val < 249 then
51
else
189)
else
(if i.val < 251 then
190
else
(if i.val < 252 then
109
else
191)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
192
else
193)
else
(if i.val < 256 then
104
else
194))
else
(if i.val < 259 then
(if i.val < 258 then
124
else
31)
else
(if i.val < 260 then
42
else
56)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
195
else
196)
else
(if i.val < 264 then
197
else
198))
else
(if i.val < 267 then
(if i.val < 266 then
40
else
199)
else
(if i.val < 268 then
200
else
(if i.val < 269 then
84
else
201)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
202
else
44)
else
(if i.val < 273 then
203
else
204))
else
(if i.val < 276 then
(if i.val < 275 then
205
else
206)
else
(if i.val < 277 then
52
else
207)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
208
else
209)
else
(if i.val < 281 then
210
else
211))
else
(if i.val < 284 then
(if i.val < 283 then
55
else
212)
else
(if i.val < 285 then
213
else
214))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
215
else
216)
else
(if i.val < 289 then
217
else
218))
else
(if i.val < 292 then
(if i.val < 291 then
219
else
220)
else
(if i.val < 293 then
221
else
28)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
222
else
223)
else
(if i.val < 297 then
149
else
156))
else
(if i.val < 300 then
(if i.val < 299 then
175
else
224)
else
(if i.val < 301 then
129
else
(if i.val < 302 then
114
else
225))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
148
else
226)
else
(if i.val < 306 then
227
else
228))
else
(if i.val < 309 then
(if i.val < 308 then
137
else
229)
else
(if i.val < 310 then
62
else
160)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
155
else
168)
else
(if i.val < 314 then
230
else
97))
else
(if i.val < 317 then
(if i.val < 316 then
231
else
95)
else
(if i.val < 318 then
169
else
(if i.val < 319 then
127
else
232)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
233
else
85)
else
(if i.val < 323 then
73
else
104))
else
(if i.val < 326 then
(if i.val < 325 then
61
else
234)
else
(if i.val < 327 then
125
else
86)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
91
else
132)
else
(if i.val < 331 then
207
else
185))
else
(if i.val < 334 then
(if i.val < 333 then
93
else
81)
else
(if i.val < 335 then
80
else
(if i.val < 336 then
235
else
135)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
236
else
237)
else
(if i.val < 340 then
238
else
212))
else
(if i.val < 343 then
(if i.val < 342 then
191
else
18)
else
(if i.val < 344 then
239
else
205)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
240
else
99)
else
(if i.val < 348 then
154
else
218))
else
(if i.val < 351 then
(if i.val < 350 then
84
else
220)
else
(if i.val < 352 then
118
else
(if i.val < 353 then
221
else
241)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
190
else
180)
else
(if i.val < 357 then
174
else
72))
else
(if i.val < 360 then
(if i.val < 359 then
77
else
63)
else
(if i.val < 361 then
242
else
3)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
5
else
59)
else
(if i.val < 365 then
243
else
58))
else
(if i.val < 368 then
(if i.val < 367 then
150
else
244)
else
(if i.val < 369 then
57
else
(if i.val < 370 then
8
else
68))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
245
else
246)
else
(if i.val < 374 then
144
else
10))
else
(if i.val < 377 then
(if i.val < 376 then
247
else
248)
else
(if i.val < 378 then
83
else
249)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
128
else
250)
else
(if i.val < 382 then
251
else
100))
else
(if i.val < 385 then
(if i.val < 384 then
116
else
162)
else
(if i.val < 386 then
96
else
(if i.val < 387 then
139
else
16)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
252
else
56)
else
(if i.val < 391 then
130
else
101))
else
(if i.val < 394 then
(if i.val < 393 then
143
else
71)
else
(if i.val < 395 then
253
else
254)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
88
else
121)
else
(if i.val < 399 then
126
else
145))
else
(if i.val < 402 then
(if i.val < 401 then
166
else
163)
else
(if i.val < 403 then
176
else
(if i.val < 404 then
76
else
255))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
216
else
131)
else
(if i.val < 408 then
15
else
107))
else
(if i.val < 411 then
(if i.val < 410 then
256
else
70)
else
(if i.val < 412 then
173
else
75)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
257
else
200)
else
(if i.val < 416 then
11
else
258))
else
(if i.val < 419 then
(if i.val < 418 then
108
else
259)
else
(if i.val < 420 then
260
else
94))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
165
else
167)
else
(if i.val < 424 then
6
else
79))
else
(if i.val < 427 then
(if i.val < 426 then
90
else
69)
else
(if i.val < 428 then
67
else
157)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
261
else
262)
else
(if i.val < 432 then
263
else
113))
else
(if i.val < 435 then
(if i.val < 434 then
110
else
264)
else
(if i.val < 436 then
109
else
(if i.val < 437 then
265
else
13))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
65
else
266)
else
(if i.val < 441 then
124
else
122))
else
(if i.val < 444 then
(if i.val < 443 then
192
else
195)
else
(if i.val < 445 then
267
else
182)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
12
else
4)
else
(if i.val < 449 then
210
else
268))
else
(if i.val < 452 then
(if i.val < 451 then
54
else
179)
else
(if i.val < 453 then
177
else
(if i.val < 454 then
269
else
87)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
270
else
271)
else
(if i.val < 458 then
89
else
272))
else
(if i.val < 461 then
(if i.val < 460 then
111
else
273)
else
(if i.val < 462 then
106
else
274)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
197
else
275)
else
(if i.val < 466 then
119
else
136))
else
(if i.val < 469 then
(if i.val < 468 then
276
else
152)
else
(if i.val < 470 then
184
else
(if i.val < 471 then
277
else
159)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
215
else
278)
else
(if i.val < 475 then
279
else
92))
else
(if i.val < 478 then
(if i.val < 477 then
280
else
74)
else
(if i.val < 479 then
281
else
282)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
283
else
219)
else
(if i.val < 483 then
102
else
202))
else
(if i.val < 486 then
(if i.val < 485 then
284
else
285)
else
(if i.val < 487 then
286
else
(if i.val < 488 then
287
else
288)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
209
else
123)
else
(if i.val < 492 then
289
else
290))
else
(if i.val < 495 then
(if i.val < 494 then
2
else
291)
else
(if i.val < 496 then
292
else
105)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
293
else
151)
else
(if i.val < 500 then
78
else
153))
else
(if i.val < 503 then
(if i.val < 502 then
9
else
294)
else
(if i.val < 504 then
295
else
(if i.val < 505 then
201
else
296))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
211
else
103)
else
(if i.val < 509 then
297
else
187))
else
(if i.val < 512 then
(if i.val < 511 then
138
else
298)
else
(if i.val < 513 then
299
else
300)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
301
else
172)
else
(if i.val < 517 then
134
else
171))
else
(if i.val < 520 then
(if i.val < 519 then
302
else
303)
else
(if i.val < 521 then
304
else
(if i.val < 522 then
189
else
188)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
305
else
306)
else
(if i.val < 526 then
307
else
112))
else
(if i.val < 529 then
(if i.val < 528 then
308
else
309)
else
(if i.val < 530 then
120
else
193)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
158
else
310)
else
(if i.val < 534 then
199
else
311))
else
(if i.val < 537 then
(if i.val < 536 then
181
else
142)
else
(if i.val < 538 then
224
else
(if i.val < 539 then
245
else
151))))))))))
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
11
else
31)
else
(if i.val < 543 then
148
else
216))
else
(if i.val < 546 then
(if i.val < 545 then
26
else
273)
else
(if i.val < 547 then
312
else
169)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
33
else
129)
else
(if i.val < 551 then
158
else
156))
else
(if i.val < 554 then
(if i.val < 553 then
252
else
264)
else
(if i.val < 555 then
313
else
204))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
236
else
290)
else
(if i.val < 559 then
314
else
234))
else
(if i.val < 562 then
(if i.val < 561 then
291
else
185)
else
(if i.val < 563 then
203
else
155)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
308
else
22)
else
(if i.val < 567 then
258
else
306))
else
(if i.val < 570 then
(if i.val < 569 then
21
else
287)
else
(if i.val < 571 then
175
else
(if i.val < 572 then
315
else
316))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
269
else
219)
else
(if i.val < 576 then
200
else
298))
else
(if i.val < 579 then
(if i.val < 578 then
317
else
231)
else
(if i.val < 580 then
5
else
130)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
292
else
263)
else
(if i.val < 584 then
30
else
176))
else
(if i.val < 587 then
(if i.val < 586 then
278
else
232)
else
(if i.val < 588 then
318
else
(if i.val < 589 then
251
else
217)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
132
else
174)
else
(if i.val < 593 then
48
else
140))
else
(if i.val < 596 then
(if i.val < 595 then
127
else
165)
else
(if i.val < 597 then
319
else
201)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
137
else
35)
else
(if i.val < 601 then
198
else
164))
else
(if i.val < 604 then
(if i.val < 603 then
38
else
268)
else
(if i.val < 605 then
320
else
(if i.val < 606 then
250
else
53)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
19
else
237)
else
(if i.val < 610 then
50
else
254))
else
(if i.val < 613 then
(if i.val < 612 then
288
else
178)
else
(if i.val < 614 then
230
else
321)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
211
else
191)
else
(if i.val < 618 then
147
else
13))
else
(if i.val < 621 then
(if i.val < 620 then
177
else
322)
else
(if i.val < 622 then
28
else
(if i.val < 623 then
188
else
242)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
190
else
323)
else
(if i.val < 627 then
136
else
152))
else
(if i.val < 630 then
(if i.val < 629 then
144
else
172)
else
(if i.val < 631 then
145
else
324)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
154
else
17)
else
(if i.val < 635 then
0
else
213))
else
(if i.val < 638 then
(if i.val < 637 then
228
else
240)
else
(if i.val < 639 then
253
else
(if i.val < 640 then
179
else
189))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
162
else
265)
else
(if i.val < 644 then
248
else
15))
else
(if i.val < 647 then
(if i.val < 646 then
225
else
8)
else
(if i.val < 648 then
206
else
223)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
325
else
302)
else
(if i.val < 652 then
14
else
128))
else
(if i.val < 655 then
(if i.val < 654 then
249
else
309)
else
(if i.val < 656 then
167
else
(if i.val < 657 then
229
else
199)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
20
else
23)
else
(if i.val < 661 then
244
else
326))
else
(if i.val < 664 then
(if i.val < 663 then
149
else
25)
else
(if i.val < 665 then
150
else
133)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
43
else
142)
else
(if i.val < 669 then
259
else
327))
else
(if i.val < 672 then
(if i.val < 671 then
187
else
32)
else
(if i.val < 673 then
328
else
(if i.val < 674 then
139
else
153))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
329
else
330)
else
(if i.val < 678 then
285
else
238))
else
(if i.val < 681 then
(if i.val < 680 then
277
else
272)
else
(if i.val < 682 then
331
else
51)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
16
else
332)
else
(if i.val < 686 then
218
else
221))
else
(if i.val < 689 then
(if i.val < 688 then
159
else
222)
else
(if i.val < 690 then
246
else
18))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
333
else
180)
else
(if i.val < 694 then
182
else
46))
else
(if i.val < 697 then
(if i.val < 696 then
334
else
135)
else
(if i.val < 698 then
233
else
170)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
143
else
195)
else
(if i.val < 702 then
209
else
212))
else
(if i.val < 705 then
(if i.val < 704 then
173
else
256)
else
(if i.val < 706 then
161
else
(if i.val < 707 then
299
else
37))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
307
else
226)
else
(if i.val < 711 then
260
else
181))
else
(if i.val < 714 then
(if i.val < 713 then
257
else
163)
else
(if i.val < 715 then
196
else
255)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
335
else
336)
else
(if i.val < 719 then
205
else
337))
else
(if i.val < 722 then
(if i.val < 721 then
338
else
10)
else
(if i.val < 723 then
34
else
(if i.val < 724 then
49
else
339)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
243
else
294)
else
(if i.val < 728 then
340
else
267))
else
(if i.val < 731 then
(if i.val < 730 then
341
else
27)
else
(if i.val < 732 then
342
else
194)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
261
else
202)
else
(if i.val < 736 then
42
else
131))
else
(if i.val < 739 then
(if i.val < 738 then
207
else
134)
else
(if i.val < 740 then
166
else
(if i.val < 741 then
210
else
39)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
171
else
160)
else
(if i.val < 745 then
343
else
183))
else
(if i.val < 748 then
(if i.val < 747 then
266
else
184)
else
(if i.val < 749 then
208
else
344)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
192
else
345)
else
(if i.val < 753 then
197
else
297))
else
(if i.val < 756 then
(if i.val < 755 then
141
else
346)
else
(if i.val < 757 then
289
else
(if i.val < 758 then
214
else
247)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
284
else
193)
else
(if i.val < 762 then
301
else
347))
else
(if i.val < 765 then
(if i.val < 764 then
220
else
348)
else
(if i.val < 766 then
281
else
286)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
241
else
305)
else
(if i.val < 770 then
271
else
349))
else
(if i.val < 773 then
(if i.val < 772 then
350
else
351)
else
(if i.val < 774 then
186
else
(if i.val < 775 then
352
else
215))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
227
else
280)
else
(if i.val < 779 then
274
else
24))
else
(if i.val < 782 then
(if i.val < 781 then
353
else
310)
else
(if i.val < 783 then
146
else
303)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
354
else
262)
else
(if i.val < 787 then
355
else
270))
else
(if i.val < 790 then
(if i.val < 789 then
168
else
295)
else
(if i.val < 791 then
138
else
(if i.val < 792 then
300
else
275)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
279
else
304)
else
(if i.val < 796 then
35
else
88))
else
(if i.val < 799 then
(if i.val < 798 then
66
else
268)
else
(if i.val < 800 then
300
else
294)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
349
else
240)
else
(if i.val < 804 then
291
else
72))
else
(if i.val < 807 then
(if i.val < 806 then
338
else
62)
else
(if i.val < 808 then
50
else
(if i.val < 809 then
313
else
280)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
83
else
54)
else
(if i.val < 813 then
292
else
87))
else
(if i.val < 816 then
(if i.val < 815 then
81
else
312)
else
(if i.val < 817 then
224
else
114)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
261
else
262)
else
(if i.val < 821 then
248
else
299))
else
(if i.val < 824 then
(if i.val < 823 then
283
else
90)
else
(if i.val < 825 then
342
else
332))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
282
else
77)
else
(if i.val < 829 then
266
else
286))
else
(if i.val < 832 then
(if i.val < 831 then
314
else
333)
else
(if i.val < 833 then
311
else
258)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
317
else
335)
else
(if i.val < 837 then
267
else
253))
else
(if i.val < 840 then
(if i.val < 839 then
275
else
351)
else
(if i.val < 841 then
307
else
(if i.val < 842 then
277
else
353))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
278
else
257)
else
(if i.val < 846 then
315
else
82))
else
(if i.val < 849 then
(if i.val < 848 then
123
else
245)
else
(if i.val < 850 then
341
else
255)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
285
else
321)
else
(if i.val < 854 then
228
else
355))
else
(if i.val < 857 then
(if i.val < 856 then
316
else
231)
else
(if i.val < 858 then
0
else
(if i.val < 859 then
91
else
24)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
37
else
232)
else
(if i.val < 863 then
334
else
340))
else
(if i.val < 866 then
(if i.val < 865 then
101
else
236)
else
(if i.val < 867 then
99
else
265)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
20
else
233)
else
(if i.val < 871 then
230
else
322))
else
(if i.val < 874 then
(if i.val < 873 then
2
else
63)
else
(if i.val < 875 then
259
else
(if i.val < 876 then
304
else
61)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
113
else
235)
else
(if i.val < 880 then
239
else
117))
else
(if i.val < 883 then
(if i.val < 882 then
57
else
320)
else
(if i.val < 884 then
89
else
354)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
293
else
331)
else
(if i.val < 888 then
53
else
225))
else
(if i.val < 891 then
(if i.val < 890 then
329
else
339)
else
(if i.val < 892 then
75
else
(if i.val < 893 then
73
else
303)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
356
else
276)
else
(if i.val < 897 then
263
else
249))
else
(if i.val < 900 then
(if i.val < 899 then
247
else
78)
else
(if i.val < 901 then
3
else
337)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
287
else
330)
else
(if i.val < 905 then
227
else
288))
else
(if i.val < 908 then
(if i.val < 907 then
252
else
67)
else
(if i.val < 909 then
305
else
(if i.val < 910 then
39
else
47))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
298
else
279)
else
(if i.val < 914 then
243
else
116))
else
(if i.val < 917 then
(if i.val < 916 then
327
else
325)
else
(if i.val < 918 then
244
else
121)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
120
else
352)
else
(if i.val < 922 then
357
else
43))
else
(if i.val < 925 then
(if i.val < 924 then
344
else
289)
else
(if i.val < 926 then
223
else
(if i.val < 927 then
238
else
254)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
271
else
94)
else
(if i.val < 931 then
1
else
302))
else
(if i.val < 934 then
(if i.val < 933 then
326
else
319)
else
(if i.val < 935 then
242
else
270)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
308
else
226)
else
(if i.val < 939 then
348
else
250))
else
(if i.val < 942 then
(if i.val < 941 then
343
else
64)
else
(if i.val < 943 then
284
else
(if i.val < 944 then
328
else
234))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
350
else
71)
else
(if i.val < 948 then
273
else
358))
else
(if i.val < 951 then
(if i.val < 950 then
229
else
290)
else
(if i.val < 952 then
297
else
324)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
19
else
318)
else
(if i.val < 956 then
306
else
269))
else
(if i.val < 959 then
(if i.val < 958 then
246
else
272)
else
(if i.val < 960 then
251
else
260))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
256
else
323)
else
(if i.val < 964 then
105
else
108))
else
(if i.val < 967 then
(if i.val < 966 then
125
else
346)
else
(if i.val < 968 then
336
else
281)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
359
else
301)
else
(if i.val < 972 then
264
else
296))
else
(if i.val < 975 then
(if i.val < 974 then
274
else
295)
else
(if i.val < 976 then
345
else
(if i.val < 977 then
310
else
241))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
309
else
93)
else
(if i.val < 981 then
347
else
98))
else
(if i.val < 984 then
(if i.val < 983 then
237
else
112)
else
(if i.val < 985 then
319
else
332)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
354
else
66)
else
(if i.val < 989 then
204
else
330))
else
(if i.val < 992 then
(if i.val < 991 then
351
else
115)
else
(if i.val < 993 then
312
else
(if i.val < 994 then
208
else
333)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
140
else
133)
else
(if i.val < 998 then
147
else
349))
else
(if i.val < 1001 then
(if i.val < 1000 then
321
else
55)
else
(if i.val < 1002 then
356
else
339)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
336
else
344)
else
(if i.val < 1006 then
60
else
328))
else
(if i.val < 1009 then
(if i.val < 1008 then
343
else
353)
else
(if i.val < 1010 then
345
else
(if i.val < 1011 then
314
else
313)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
355
else
357)
else
(if i.val < 1015 then
329
else
194))
else
(if i.val < 1018 then
(if i.val < 1017 then
164
else
340)
else
(if i.val < 1019 then
325
else
348)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
331
else
217)
else
(if i.val < 1023 then
315
else
341))
else
(if i.val < 1026 then
(if i.val < 1025 then
359
else
317)
else
(if i.val < 1027 then
350
else
(if i.val < 1028 then
327
else
64)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
338
else
346)
else
(if i.val < 1032 then
14
else
318))
else
(if i.val < 1035 then
(if i.val < 1034 then
352
else
170)
else
(if i.val < 1036 then
213
else
326)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
196
else
347)
else
(if i.val < 1040 then
214
else
146))
else
(if i.val < 1043 then
(if i.val < 1042 then
342
else
117)
else
(if i.val < 1044 then
161
else
(if i.val < 1045 then
322
else
17))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
98
else
178)
else
(if i.val < 1049 then
320
else
316))
else
(if i.val < 1052 then
(if i.val < 1051 then
141
else
206)
else
(if i.val < 1053 then
7
else
334)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
358
else
222)
else
(if i.val < 1057 then
82
else
335))
else
(if i.val < 1060 then
(if i.val < 1059 then
186
else
324)
else
(if i.val < 1061 then
203
else
(if i.val < 1062 then
337
else
323)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
183
else
198)
else
(if i.val < 1066 then
283
else
235))
else
(if i.val < 1069 then
(if i.val < 1068 then
311
else
157)
else
(if i.val < 1070 then
356
else
296)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
359
else
357)
else
(if i.val < 1074 then
282
else
358))
else
(if i.val < 1077 then
(if i.val < 1076 then
47
else
293)
else
(if i.val < 1078 then
239
else
(if i.val < 1079 then
276
else
41)))))))))))

def g32p_row06_cosetDistances0 : Fin 1080 → ℕ :=
  fun i => (if i.val < 540 then
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
2)
else
(if i.val < 31 then
0
else
(if i.val < 32 then
0
else
0))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
0
else
0)
else
(if i.val < 36 then
0
else
0))
else
(if i.val < 39 then
(if i.val < 38 then
0
else
0)
else
(if i.val < 40 then
0
else
0)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
0
else
0)
else
(if i.val < 44 then
0
else
0))
else
(if i.val < 47 then
(if i.val < 46 then
0
else
0)
else
(if i.val < 48 then
0
else
(if i.val < 49 then
0
else
0)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
0
else
0)
else
(if i.val < 53 then
0
else
0))
else
(if i.val < 56 then
(if i.val < 55 then
0
else
0)
else
(if i.val < 57 then
0
else
2)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
0
else
0)
else
(if i.val < 61 then
0
else
0))
else
(if i.val < 64 then
(if i.val < 63 then
0
else
0)
else
(if i.val < 65 then
0
else
(if i.val < 66 then
0
else
0)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
0
else
0)
else
(if i.val < 70 then
0
else
0))
else
(if i.val < 73 then
(if i.val < 72 then
0
else
0)
else
(if i.val < 74 then
0
else
0)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
0
else
0)
else
(if i.val < 78 then
0
else
0))
else
(if i.val < 81 then
(if i.val < 80 then
0
else
2)
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
1
else
0)
else
(if i.val < 87 then
0
else
0))
else
(if i.val < 90 then
(if i.val < 89 then
0
else
0)
else
(if i.val < 91 then
0
else
0)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
2
else
0)
else
(if i.val < 95 then
0
else
0))
else
(if i.val < 98 then
(if i.val < 97 then
0
else
0)
else
(if i.val < 99 then
0
else
(if i.val < 100 then
0
else
0))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
0
else
0)
else
(if i.val < 104 then
0
else
0))
else
(if i.val < 107 then
(if i.val < 106 then
0
else
1)
else
(if i.val < 108 then
0
else
0)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
0
else
0)
else
(if i.val < 112 then
0
else
0))
else
(if i.val < 115 then
(if i.val < 114 then
0
else
0)
else
(if i.val < 116 then
0
else
(if i.val < 117 then
2
else
0)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
0
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
0
else
0)
else
(if i.val < 125 then
0
else
0)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
0
else
1)
else
(if i.val < 129 then
0
else
0))
else
(if i.val < 132 then
(if i.val < 131 then
0
else
0)
else
(if i.val < 133 then
0
else
(if i.val < 134 then
0
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
0
else
0)
else
(if i.val < 138 then
0
else
0))
else
(if i.val < 141 then
(if i.val < 140 then
0
else
0)
else
(if i.val < 142 then
0
else
1)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
0
else
2)
else
(if i.val < 146 then
1
else
1))
else
(if i.val < 149 then
(if i.val < 148 then
2
else
0)
else
(if i.val < 150 then
0
else
0))))
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
0))
else
(if i.val < 157 then
(if i.val < 156 then
1
else
1)
else
(if i.val < 158 then
0
else
0)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
1
else
0)
else
(if i.val < 162 then
0
else
0))
else
(if i.val < 165 then
(if i.val < 164 then
0
else
2)
else
(if i.val < 166 then
0
else
(if i.val < 167 then
0
else
2))))))
else
(if i.val < 185 then
(if i.val < 176 then
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
0)))
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
1))
else
(if i.val < 182 then
(if i.val < 181 then
1
else
1)
else
(if i.val < 183 then
0
else
(if i.val < 184 then
0
else
0)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
2
else
0)
else
(if i.val < 188 then
0
else
1))
else
(if i.val < 191 then
(if i.val < 190 then
0
else
1)
else
(if i.val < 192 then
0
else
0)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
1
else
2)
else
(if i.val < 196 then
1
else
0))
else
(if i.val < 199 then
(if i.val < 198 then
1
else
2)
else
(if i.val < 200 then
0
else
(if i.val < 201 then
2
else
0)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
0
else
0)
else
(if i.val < 205 then
2
else
0))
else
(if i.val < 208 then
(if i.val < 207 then
2
else
1)
else
(if i.val < 209 then
1
else
0)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
2
else
2)
else
(if i.val < 213 then
0
else
2))
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
0)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
2
else
0)
else
(if i.val < 222 then
1
else
1))
else
(if i.val < 225 then
(if i.val < 224 then
0
else
0)
else
(if i.val < 226 then
0
else
2)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
2
else
1)
else
(if i.val < 230 then
0
else
2))
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
0
else
0))
else
(if i.val < 242 then
(if i.val < 241 then
0
else
0)
else
(if i.val < 243 then
0
else
1)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
2
else
0)
else
(if i.val < 247 then
0
else
0))
else
(if i.val < 250 then
(if i.val < 249 then
2
else
0)
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
0
else
0)
else
(if i.val < 256 then
1
else
0))
else
(if i.val < 259 then
(if i.val < 258 then
1
else
2)
else
(if i.val < 260 then
2
else
1)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
0
else
0)
else
(if i.val < 264 then
0
else
0))
else
(if i.val < 267 then
(if i.val < 266 then
2
else
0)
else
(if i.val < 268 then
0
else
(if i.val < 269 then
1
else
0)))))))))
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
2)
else
(if i.val < 273 then
0
else
0))
else
(if i.val < 276 then
(if i.val < 275 then
0
else
0)
else
(if i.val < 277 then
2
else
0)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
0
else
0)
else
(if i.val < 281 then
0
else
0))
else
(if i.val < 284 then
(if i.val < 283 then
1
else
0)
else
(if i.val < 285 then
0
else
0))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
0
else
0)
else
(if i.val < 289 then
0
else
0))
else
(if i.val < 292 then
(if i.val < 291 then
0
else
0)
else
(if i.val < 293 then
0
else
2)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
0
else
0)
else
(if i.val < 297 then
1
else
1))
else
(if i.val < 300 then
(if i.val < 299 then
1
else
0)
else
(if i.val < 301 then
1
else
(if i.val < 302 then
2
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
0
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
2
else
1)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
1
else
1)
else
(if i.val < 314 then
0
else
2))
else
(if i.val < 317 then
(if i.val < 316 then
0
else
2)
else
(if i.val < 318 then
1
else
(if i.val < 319 then
1
else
0)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
0
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
0)
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
1)
else
(if i.val < 331 then
1
else
1))
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
0
else
0)
else
(if i.val < 340 then
0
else
1))
else
(if i.val < 343 then
(if i.val < 342 then
1
else
1)
else
(if i.val < 344 then
0
else
1)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
0
else
2)
else
(if i.val < 348 then
1
else
1))
else
(if i.val < 351 then
(if i.val < 350 then
2
else
1)
else
(if i.val < 352 then
2
else
(if i.val < 353 then
1
else
0)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
1
else
1)
else
(if i.val < 357 then
1
else
2))
else
(if i.val < 360 then
(if i.val < 359 then
2
else
2)
else
(if i.val < 361 then
0
else
2)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
1
else
2)
else
(if i.val < 365 then
0
else
2))
else
(if i.val < 368 then
(if i.val < 367 then
1
else
0)
else
(if i.val < 369 then
2
else
(if i.val < 370 then
1
else
2))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
0
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
0)
else
(if i.val < 378 then
2
else
0)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
1
else
0)
else
(if i.val < 382 then
0
else
2))
else
(if i.val < 385 then
(if i.val < 384 then
2
else
1)
else
(if i.val < 386 then
2
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
2)
else
(if i.val < 391 then
1
else
2))
else
(if i.val < 394 then
(if i.val < 393 then
1
else
2)
else
(if i.val < 395 then
0
else
0)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
2
else
2)
else
(if i.val < 399 then
2
else
1))
else
(if i.val < 402 then
(if i.val < 401 then
1
else
1)
else
(if i.val < 403 then
1
else
(if i.val < 404 then
2
else
0))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
1
else
1)
else
(if i.val < 408 then
1
else
2))
else
(if i.val < 411 then
(if i.val < 410 then
0
else
2)
else
(if i.val < 412 then
1
else
2)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
0
else
1)
else
(if i.val < 416 then
1
else
0))
else
(if i.val < 419 then
(if i.val < 418 then
2
else
0)
else
(if i.val < 420 then
0
else
2))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
1
else
1)
else
(if i.val < 424 then
1
else
2))
else
(if i.val < 427 then
(if i.val < 426 then
2
else
2)
else
(if i.val < 428 then
2
else
1)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
0
else
0)
else
(if i.val < 432 then
0
else
2))
else
(if i.val < 435 then
(if i.val < 434 then
2
else
0)
else
(if i.val < 436 then
2
else
(if i.val < 437 then
0
else
1))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
2
else
0)
else
(if i.val < 441 then
2
else
2))
else
(if i.val < 444 then
(if i.val < 443 then
1
else
1)
else
(if i.val < 445 then
0
else
1)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
1
else
2)
else
(if i.val < 449 then
1
else
0))
else
(if i.val < 452 then
(if i.val < 451 then
2
else
1)
else
(if i.val < 453 then
1
else
(if i.val < 454 then
0
else
2)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
0
else
0)
else
(if i.val < 458 then
2
else
0))
else
(if i.val < 461 then
(if i.val < 460 then
2
else
0)
else
(if i.val < 462 then
2
else
0)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
1
else
0)
else
(if i.val < 466 then
2
else
1))
else
(if i.val < 469 then
(if i.val < 468 then
0
else
1)
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
1
else
0)
else
(if i.val < 475 then
0
else
2))
else
(if i.val < 478 then
(if i.val < 477 then
0
else
2)
else
(if i.val < 479 then
0
else
0)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
0
else
1)
else
(if i.val < 483 then
2
else
1))
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
(if i.val < 488 then
0
else
0)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
1
else
2)
else
(if i.val < 492 then
0
else
0))
else
(if i.val < 495 then
(if i.val < 494 then
2
else
0)
else
(if i.val < 496 then
0
else
2)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
0
else
1)
else
(if i.val < 500 then
2
else
1))
else
(if i.val < 503 then
(if i.val < 502 then
1
else
0)
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
2)
else
(if i.val < 509 then
0
else
1))
else
(if i.val < 512 then
(if i.val < 511 then
1
else
0)
else
(if i.val < 513 then
0
else
0)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
0
else
1)
else
(if i.val < 517 then
1
else
1))
else
(if i.val < 520 then
(if i.val < 519 then
0
else
0)
else
(if i.val < 521 then
0
else
(if i.val < 522 then
1
else
1)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
0
else
0)
else
(if i.val < 526 then
0
else
2))
else
(if i.val < 529 then
(if i.val < 528 then
0
else
0)
else
(if i.val < 530 then
2
else
1)))
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
1)
else
(if i.val < 538 then
1
else
(if i.val < 539 then
1
else
2))))))))))
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
2
else
1)
else
(if i.val < 543 then
2
else
2))
else
(if i.val < 546 then
(if i.val < 545 then
1
else
1)
else
(if i.val < 547 then
0
else
2)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
1
else
2)
else
(if i.val < 551 then
2
else
2))
else
(if i.val < 554 then
(if i.val < 553 then
1
else
1)
else
(if i.val < 555 then
0
else
2))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
1
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
1
else
2)
else
(if i.val < 563 then
2
else
2)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
1
else
1)
else
(if i.val < 567 then
1
else
1))
else
(if i.val < 570 then
(if i.val < 569 then
1
else
1)
else
(if i.val < 571 then
2
else
(if i.val < 572 then
0
else
0))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
1
else
2)
else
(if i.val < 576 then
2
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
2
else
2)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
1
else
1)
else
(if i.val < 584 then
1
else
2))
else
(if i.val < 587 then
(if i.val < 586 then
1
else
1)
else
(if i.val < 588 then
0
else
(if i.val < 589 then
1
else
2)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
2
else
2)
else
(if i.val < 593 then
1
else
2))
else
(if i.val < 596 then
(if i.val < 595 then
2
else
2)
else
(if i.val < 597 then
0
else
2)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
2
else
1)
else
(if i.val < 601 then
2
else
2))
else
(if i.val < 604 then
(if i.val < 603 then
1
else
1)
else
(if i.val < 605 then
0
else
(if i.val < 606 then
1
else
1)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
1
else
1)
else
(if i.val < 610 then
1
else
1))
else
(if i.val < 613 then
(if i.val < 612 then
1
else
2)
else
(if i.val < 614 then
1
else
0)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
2
else
2)
else
(if i.val < 618 then
2
else
2))
else
(if i.val < 621 then
(if i.val < 620 then
2
else
0)
else
(if i.val < 622 then
1
else
(if i.val < 623 then
2
else
1)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
2
else
0)
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
0)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
2
else
2)
else
(if i.val < 635 then
1
else
2))
else
(if i.val < 638 then
(if i.val < 637 then
1
else
1)
else
(if i.val < 639 then
1
else
(if i.val < 640 then
2
else
2))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
2
else
1)
else
(if i.val < 644 then
1
else
2))
else
(if i.val < 647 then
(if i.val < 646 then
1
else
2)
else
(if i.val < 648 then
2
else
1)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
0
else
1)
else
(if i.val < 652 then
2
else
2))
else
(if i.val < 655 then
(if i.val < 654 then
1
else
1)
else
(if i.val < 656 then
2
else
(if i.val < 657 then
1
else
2)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
1
else
1)
else
(if i.val < 661 then
1
else
0))
else
(if i.val < 664 then
(if i.val < 663 then
2
else
1)
else
(if i.val < 665 then
2
else
2)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
1
else
2)
else
(if i.val < 669 then
1
else
0))
else
(if i.val < 672 then
(if i.val < 671 then
2
else
1)
else
(if i.val < 673 then
0
else
(if i.val < 674 then
2
else
2))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
0
else
0)
else
(if i.val < 678 then
1
else
1))
else
(if i.val < 681 then
(if i.val < 680 then
1
else
1)
else
(if i.val < 682 then
0
else
1)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
2
else
0)
else
(if i.val < 686 then
2
else
2))
else
(if i.val < 689 then
(if i.val < 688 then
2
else
2)
else
(if i.val < 690 then
1
else
2))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
0
else
2)
else
(if i.val < 694 then
2
else
1))
else
(if i.val < 697 then
(if i.val < 696 then
0
else
2)
else
(if i.val < 698 then
1
else
2)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
2
else
2)
else
(if i.val < 702 then
2
else
2))
else
(if i.val < 705 then
(if i.val < 704 then
2
else
1)
else
(if i.val < 706 then
2
else
(if i.val < 707 then
1
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
1
else
2))
else
(if i.val < 714 then
(if i.val < 713 then
1
else
2)
else
(if i.val < 715 then
2
else
1)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
0
else
0)
else
(if i.val < 719 then
2
else
0))
else
(if i.val < 722 then
(if i.val < 721 then
0
else
2)
else
(if i.val < 723 then
1
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
1
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
2)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
1
else
2)
else
(if i.val < 736 then
1
else
2))
else
(if i.val < 739 then
(if i.val < 738 then
2
else
2)
else
(if i.val < 740 then
2
else
(if i.val < 741 then
2
else
1)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
2
else
2)
else
(if i.val < 745 then
0
else
2))
else
(if i.val < 748 then
(if i.val < 747 then
1
else
2)
else
(if i.val < 749 then
2
else
0)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
2
else
0)
else
(if i.val < 753 then
2
else
1))
else
(if i.val < 756 then
(if i.val < 755 then
2
else
0)
else
(if i.val < 757 then
1
else
(if i.val < 758 then
2
else
1)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
1
else
2)
else
(if i.val < 762 then
1
else
0))
else
(if i.val < 765 then
(if i.val < 764 then
2
else
0)
else
(if i.val < 766 then
1
else
1)))
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
0))
else
(if i.val < 773 then
(if i.val < 772 then
0
else
0)
else
(if i.val < 774 then
2
else
(if i.val < 775 then
0
else
2))))))
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
1
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
2
else
1)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
0
else
1)
else
(if i.val < 787 then
0
else
1))
else
(if i.val < 790 then
(if i.val < 789 then
2
else
1)
else
(if i.val < 791 then
2
else
(if i.val < 792 then
1
else
1)))))
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
2
else
1))
else
(if i.val < 799 then
(if i.val < 798 then
1
else
2)
else
(if i.val < 800 then
2
else
2)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
1
else
2)
else
(if i.val < 804 then
2
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
2
else
(if i.val < 809 then
1
else
2)))))))))
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
1)
else
(if i.val < 813 then
2
else
1))
else
(if i.val < 816 then
(if i.val < 815 then
1
else
1)
else
(if i.val < 817 then
2
else
1)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
2
else
2)
else
(if i.val < 821 then
2
else
2))
else
(if i.val < 824 then
(if i.val < 823 then
2
else
1)
else
(if i.val < 825 then
1
else
1))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
2
else
1)
else
(if i.val < 829 then
2
else
2))
else
(if i.val < 832 then
(if i.val < 831 then
1
else
1)
else
(if i.val < 833 then
2
else
2)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
1
else
1)
else
(if i.val < 837 then
2
else
2))
else
(if i.val < 840 then
(if i.val < 839 then
2
else
1)
else
(if i.val < 841 then
2
else
(if i.val < 842 then
2
else
1))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
2
else
2)
else
(if i.val < 846 then
1
else
1))
else
(if i.val < 849 then
(if i.val < 848 then
1
else
2)
else
(if i.val < 850 then
1
else
2)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
2
else
1)
else
(if i.val < 854 then
2
else
1))
else
(if i.val < 857 then
(if i.val < 856 then
1
else
2)
else
(if i.val < 858 then
2
else
(if i.val < 859 then
1
else
2)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
2
else
2)
else
(if i.val < 863 then
1
else
1))
else
(if i.val < 866 then
(if i.val < 865 then
1
else
2)
else
(if i.val < 867 then
1
else
2)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
2
else
2)
else
(if i.val < 871 then
2
else
1))
else
(if i.val < 874 then
(if i.val < 873 then
1
else
1)
else
(if i.val < 875 then
2
else
(if i.val < 876 then
2
else
1)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
1
else
2)
else
(if i.val < 880 then
2
else
1))
else
(if i.val < 883 then
(if i.val < 882 then
1
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
2
else
1)
else
(if i.val < 888 then
2
else
2))
else
(if i.val < 891 then
(if i.val < 890 then
1
else
1)
else
(if i.val < 892 then
1
else
(if i.val < 893 then
1
else
2)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
0
else
2)
else
(if i.val < 897 then
2
else
2))
else
(if i.val < 900 then
(if i.val < 899 then
2
else
1)
else
(if i.val < 901 then
1
else
1)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
2
else
1)
else
(if i.val < 905 then
2
else
2))
else
(if i.val < 908 then
(if i.val < 907 then
2
else
1)
else
(if i.val < 909 then
2
else
(if i.val < 910 then
2
else
2))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
2
else
2)
else
(if i.val < 914 then
2
else
1))
else
(if i.val < 917 then
(if i.val < 916 then
1
else
1)
else
(if i.val < 918 then
2
else
1)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
1
else
1)
else
(if i.val < 922 then
0
else
2))
else
(if i.val < 925 then
(if i.val < 924 then
1
else
2)
else
(if i.val < 926 then
2
else
(if i.val < 927 then
2
else
2)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
2
else
1)
else
(if i.val < 931 then
1
else
2))
else
(if i.val < 934 then
(if i.val < 933 then
1
else
1)
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
1
else
2))
else
(if i.val < 942 then
(if i.val < 941 then
1
else
1)
else
(if i.val < 943 then
2
else
(if i.val < 944 then
1
else
2))))))))
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
1)
else
(if i.val < 948 then
2
else
0))
else
(if i.val < 951 then
(if i.val < 950 then
2
else
2)
else
(if i.val < 952 then
2
else
1)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
2
else
1)
else
(if i.val < 956 then
2
else
2))
else
(if i.val < 959 then
(if i.val < 958 then
2
else
2)
else
(if i.val < 960 then
2
else
2))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
2
else
1)
else
(if i.val < 964 then
1
else
1))
else
(if i.val < 967 then
(if i.val < 966 then
1
else
1)
else
(if i.val < 968 then
1
else
2)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
0
else
2)
else
(if i.val < 972 then
2
else
2))
else
(if i.val < 975 then
(if i.val < 974 then
2
else
2)
else
(if i.val < 976 then
1
else
(if i.val < 977 then
2
else
2))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
2
else
1)
else
(if i.val < 981 then
1
else
1))
else
(if i.val < 984 then
(if i.val < 983 then
2
else
1)
else
(if i.val < 985 then
2
else
2)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
2
else
2)
else
(if i.val < 989 then
1
else
2))
else
(if i.val < 992 then
(if i.val < 991 then
2
else
2)
else
(if i.val < 993 then
2
else
(if i.val < 994 then
1
else
2)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
1
else
1)
else
(if i.val < 998 then
1
else
2))
else
(if i.val < 1001 then
(if i.val < 1000 then
2
else
2)
else
(if i.val < 1002 then
1
else
2)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
2
else
2)
else
(if i.val < 1006 then
2
else
2))
else
(if i.val < 1009 then
(if i.val < 1008 then
2
else
2)
else
(if i.val < 1010 then
2
else
(if i.val < 1011 then
2
else
2)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
2
else
1)
else
(if i.val < 1015 then
2
else
1))
else
(if i.val < 1018 then
(if i.val < 1017 then
1
else
2)
else
(if i.val < 1019 then
2
else
2)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
2
else
1)
else
(if i.val < 1023 then
2
else
2))
else
(if i.val < 1026 then
(if i.val < 1025 then
1
else
2)
else
(if i.val < 1027 then
2
else
(if i.val < 1028 then
2
else
2)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
2
else
2)
else
(if i.val < 1032 then
1
else
2))
else
(if i.val < 1035 then
(if i.val < 1034 then
2
else
1)
else
(if i.val < 1036 then
1
else
2)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
1
else
2)
else
(if i.val < 1040 then
1
else
1))
else
(if i.val < 1043 then
(if i.val < 1042 then
2
else
2)
else
(if i.val < 1044 then
1
else
(if i.val < 1045 then
2
else
1))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
2
else
1)
else
(if i.val < 1049 then
2
else
2))
else
(if i.val < 1052 then
(if i.val < 1051 then
1
else
1)
else
(if i.val < 1053 then
1
else
2)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
1
else
1)
else
(if i.val < 1057 then
2
else
2))
else
(if i.val < 1060 then
(if i.val < 1059 then
1
else
2)
else
(if i.val < 1061 then
1
else
(if i.val < 1062 then
2
else
2)))))
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
1
else
1))
else
(if i.val < 1069 then
(if i.val < 1068 then
1
else
2)
else
(if i.val < 1070 then
2
else
1)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
2
else
2)
else
(if i.val < 1074 then
1
else
2))
else
(if i.val < 1077 then
(if i.val < 1076 then
1
else
1)
else
(if i.val < 1078 then
1
else
(if i.val < 1079 then
1
else
1)))))))))))

def g32p_row06_cosetRoots0 : Fin 360 → Fin 1080 :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
0
else
1)
else
(if i.val < 3 then
2
else
(if i.val < 4 then
3
else
4)))
else
(if i.val < 8 then
(if i.val < 6 then
5
else
(if i.val < 7 then
6
else
7))
else
(if i.val < 9 then
8
else
(if i.val < 10 then
9
else
10))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
11
else
12)
else
(if i.val < 14 then
13
else
(if i.val < 15 then
14
else
15)))
else
(if i.val < 19 then
(if i.val < 17 then
16
else
(if i.val < 18 then
17
else
18))
else
(if i.val < 20 then
19
else
(if i.val < 21 then
20
else
21)))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
22
else
23)
else
(if i.val < 25 then
24
else
(if i.val < 26 then
25
else
26)))
else
(if i.val < 30 then
(if i.val < 28 then
27
else
(if i.val < 29 then
28
else
30))
else
(if i.val < 31 then
31
else
(if i.val < 32 then
32
else
33))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
34
else
(if i.val < 35 then
35
else
36))
else
(if i.val < 37 then
37
else
(if i.val < 38 then
38
else
39)))
else
(if i.val < 42 then
(if i.val < 40 then
40
else
(if i.val < 41 then
41
else
42))
else
(if i.val < 43 then
43
else
(if i.val < 44 then
44
else
45))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
46
else
47)
else
(if i.val < 48 then
48
else
(if i.val < 49 then
49
else
50)))
else
(if i.val < 53 then
(if i.val < 51 then
51
else
(if i.val < 52 then
52
else
53))
else
(if i.val < 54 then
54
else
(if i.val < 55 then
55
else
56))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
58
else
59)
else
(if i.val < 59 then
60
else
(if i.val < 60 then
61
else
62)))
else
(if i.val < 64 then
(if i.val < 62 then
63
else
(if i.val < 63 then
64
else
65))
else
(if i.val < 65 then
66
else
(if i.val < 66 then
67
else
68)))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
69
else
70)
else
(if i.val < 70 then
71
else
(if i.val < 71 then
72
else
73)))
else
(if i.val < 75 then
(if i.val < 73 then
74
else
(if i.val < 74 then
75
else
76))
else
(if i.val < 76 then
77
else
(if i.val < 77 then
78
else
79))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
82
else
(if i.val < 80 then
85
else
86))
else
(if i.val < 82 then
87
else
(if i.val < 83 then
88
else
89)))
else
(if i.val < 87 then
(if i.val < 85 then
90
else
(if i.val < 86 then
91
else
93))
else
(if i.val < 88 then
94
else
(if i.val < 89 then
95
else
96)))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
97
else
98)
else
(if i.val < 93 then
99
else
(if i.val < 94 then
100
else
101)))
else
(if i.val < 98 then
(if i.val < 96 then
102
else
(if i.val < 97 then
103
else
104))
else
(if i.val < 99 then
105
else
(if i.val < 100 then
107
else
108))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
109
else
110)
else
(if i.val < 104 then
111
else
(if i.val < 105 then
112
else
113)))
else
(if i.val < 109 then
(if i.val < 107 then
114
else
(if i.val < 108 then
115
else
117))
else
(if i.val < 110 then
118
else
(if i.val < 111 then
119
else
121)))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
122
else
123)
else
(if i.val < 115 then
124
else
(if i.val < 116 then
125
else
126)))
else
(if i.val < 120 then
(if i.val < 118 then
128
else
(if i.val < 119 then
129
else
130))
else
(if i.val < 121 then
131
else
(if i.val < 122 then
132
else
133))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
134
else
(if i.val < 125 then
135
else
136))
else
(if i.val < 127 then
137
else
(if i.val < 128 then
138
else
139)))
else
(if i.val < 132 then
(if i.val < 130 then
140
else
(if i.val < 131 then
141
else
143))
else
(if i.val < 133 then
148
else
(if i.val < 134 then
149
else
150))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
151
else
153)
else
(if i.val < 138 then
154
else
(if i.val < 139 then
157
else
158)))
else
(if i.val < 143 then
(if i.val < 141 then
160
else
(if i.val < 142 then
161
else
162))
else
(if i.val < 144 then
163
else
(if i.val < 145 then
165
else
166))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
168
else
169)
else
(if i.val < 149 then
170
else
(if i.val < 150 then
172
else
174)))
else
(if i.val < 154 then
(if i.val < 152 then
175
else
(if i.val < 153 then
176
else
177))
else
(if i.val < 155 then
182
else
(if i.val < 156 then
183
else
184)))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
186
else
187)
else
(if i.val < 160 then
189
else
(if i.val < 161 then
191
else
192)))
else
(if i.val < 165 then
(if i.val < 163 then
196
else
(if i.val < 164 then
199
else
201))
else
(if i.val < 166 then
202
else
(if i.val < 167 then
203
else
205))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
209
else
(if i.val < 170 then
212
else
214))
else
(if i.val < 172 then
216
else
(if i.val < 173 then
218
else
220)))
else
(if i.val < 177 then
(if i.val < 175 then
223
else
(if i.val < 176 then
224
else
225))
else
(if i.val < 178 then
229
else
(if i.val < 179 then
232
else
235))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
237
else
238)
else
(if i.val < 183 then
239
else
(if i.val < 184 then
240
else
241)))
else
(if i.val < 188 then
(if i.val < 186 then
242
else
(if i.val < 187 then
245
else
246))
else
(if i.val < 189 then
247
else
(if i.val < 190 then
249
else
250))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
252
else
253)
else
(if i.val < 194 then
254
else
(if i.val < 195 then
256
else
261)))
else
(if i.val < 199 then
(if i.val < 197 then
262
else
(if i.val < 198 then
263
else
264))
else
(if i.val < 200 then
266
else
(if i.val < 201 then
267
else
269)))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
270
else
272)
else
(if i.val < 205 then
273
else
(if i.val < 206 then
274
else
275)))
else
(if i.val < 210 then
(if i.val < 208 then
277
else
(if i.val < 209 then
278
else
279))
else
(if i.val < 211 then
280
else
(if i.val < 212 then
281
else
283))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
284
else
(if i.val < 215 then
285
else
286))
else
(if i.val < 217 then
287
else
(if i.val < 218 then
288
else
289)))
else
(if i.val < 222 then
(if i.val < 220 then
290
else
(if i.val < 221 then
291
else
292))
else
(if i.val < 223 then
294
else
(if i.val < 224 then
295
else
299))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
302
else
304)
else
(if i.val < 228 then
305
else
(if i.val < 229 then
306
else
308)))
else
(if i.val < 233 then
(if i.val < 231 then
313
else
(if i.val < 232 then
315
else
319))
else
(if i.val < 234 then
320
else
(if i.val < 235 then
325
else
335))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
337
else
338)
else
(if i.val < 239 then
339
else
(if i.val < 240 then
343
else
345)))
else
(if i.val < 244 then
(if i.val < 242 then
353
else
(if i.val < 243 then
360
else
364))
else
(if i.val < 245 then
367
else
(if i.val < 246 then
371
else
372)))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
375
else
376)
else
(if i.val < 250 then
378
else
(if i.val < 251 then
380
else
381)))
else
(if i.val < 255 then
(if i.val < 253 then
388
else
(if i.val < 254 then
394
else
395))
else
(if i.val < 256 then
404
else
(if i.val < 257 then
409
else
413))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
416
else
(if i.val < 260 then
418
else
419))
else
(if i.val < 262 then
429
else
(if i.val < 263 then
430
else
431)))
else
(if i.val < 267 then
(if i.val < 265 then
434
else
(if i.val < 266 then
436
else
439))
else
(if i.val < 268 then
444
else
(if i.val < 269 then
449
else
453)))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
455
else
456)
else
(if i.val < 273 then
458
else
(if i.val < 274 then
460
else
462)))
else
(if i.val < 278 then
(if i.val < 276 then
464
else
(if i.val < 277 then
467
else
470))
else
(if i.val < 279 then
473
else
(if i.val < 280 then
474
else
476))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
478
else
479)
else
(if i.val < 284 then
480
else
(if i.val < 285 then
484
else
485)))
else
(if i.val < 289 then
(if i.val < 287 then
486
else
(if i.val < 288 then
487
else
488))
else
(if i.val < 290 then
491
else
(if i.val < 291 then
492
else
494)))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
495
else
497)
else
(if i.val < 295 then
502
else
(if i.val < 296 then
503
else
505)))
else
(if i.val < 300 then
(if i.val < 298 then
508
else
(if i.val < 299 then
511
else
512))
else
(if i.val < 301 then
513
else
(if i.val < 302 then
514
else
518))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
519
else
(if i.val < 305 then
520
else
523))
else
(if i.val < 307 then
524
else
(if i.val < 308 then
525
else
527)))
else
(if i.val < 312 then
(if i.val < 310 then
528
else
(if i.val < 311 then
532
else
534))
else
(if i.val < 313 then
546
else
(if i.val < 314 then
554
else
558))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
571
else
572)
else
(if i.val < 318 then
577
else
(if i.val < 319 then
587
else
596)))
else
(if i.val < 323 then
(if i.val < 321 then
604
else
(if i.val < 322 then
614
else
620))
else
(if i.val < 324 then
625
else
(if i.val < 325 then
631
else
649))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
661
else
669)
else
(if i.val < 329 then
672
else
(if i.val < 330 then
675
else
676)))
else
(if i.val < 334 then
(if i.val < 332 then
681
else
(if i.val < 333 then
684
else
691))
else
(if i.val < 335 then
695
else
(if i.val < 336 then
716
else
717)))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
719
else
720)
else
(if i.val < 340 then
724
else
(if i.val < 341 then
727
else
729)))
else
(if i.val < 345 then
(if i.val < 343 then
731
else
(if i.val < 344 then
744
else
749))
else
(if i.val < 346 then
751
else
(if i.val < 347 then
755
else
762))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
764
else
(if i.val < 350 then
770
else
771))
else
(if i.val < 352 then
772
else
(if i.val < 353 then
774
else
780)))
else
(if i.val < 357 then
(if i.val < 355 then
784
else
(if i.val < 356 then
786
else
894))
else
(if i.val < 358 then
921
else
(if i.val < 359 then
948
else
969)))))))))

def g32p_row06_cosetLengths0 : Fin 360 → ℕ :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
3
else
3)
else
(if i.val < 3 then
3
else
(if i.val < 4 then
3
else
3)))
else
(if i.val < 8 then
(if i.val < 6 then
3
else
(if i.val < 7 then
3
else
3))
else
(if i.val < 9 then
3
else
(if i.val < 10 then
3
else
3))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
3
else
3)
else
(if i.val < 14 then
3
else
(if i.val < 15 then
3
else
3)))
else
(if i.val < 19 then
(if i.val < 17 then
3
else
(if i.val < 18 then
3
else
3))
else
(if i.val < 20 then
3
else
(if i.val < 21 then
3
else
3)))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
3
else
3)
else
(if i.val < 25 then
3
else
(if i.val < 26 then
3
else
3)))
else
(if i.val < 30 then
(if i.val < 28 then
3
else
(if i.val < 29 then
3
else
3))
else
(if i.val < 31 then
3
else
(if i.val < 32 then
3
else
3))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
3
else
(if i.val < 35 then
3
else
3))
else
(if i.val < 37 then
3
else
(if i.val < 38 then
3
else
3)))
else
(if i.val < 42 then
(if i.val < 40 then
3
else
(if i.val < 41 then
3
else
3))
else
(if i.val < 43 then
3
else
(if i.val < 44 then
3
else
3))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
3
else
3)
else
(if i.val < 48 then
3
else
(if i.val < 49 then
3
else
3)))
else
(if i.val < 53 then
(if i.val < 51 then
3
else
(if i.val < 52 then
3
else
3))
else
(if i.val < 54 then
3
else
(if i.val < 55 then
3
else
3))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
3
else
3)
else
(if i.val < 59 then
3
else
(if i.val < 60 then
3
else
3)))
else
(if i.val < 64 then
(if i.val < 62 then
3
else
(if i.val < 63 then
3
else
3))
else
(if i.val < 65 then
3
else
(if i.val < 66 then
3
else
3)))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
3
else
3)
else
(if i.val < 70 then
3
else
(if i.val < 71 then
3
else
3)))
else
(if i.val < 75 then
(if i.val < 73 then
3
else
(if i.val < 74 then
3
else
3))
else
(if i.val < 76 then
3
else
(if i.val < 77 then
3
else
3))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
3
else
(if i.val < 80 then
3
else
3))
else
(if i.val < 82 then
3
else
(if i.val < 83 then
3
else
3)))
else
(if i.val < 87 then
(if i.val < 85 then
3
else
(if i.val < 86 then
3
else
3))
else
(if i.val < 88 then
3
else
(if i.val < 89 then
3
else
3)))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
3
else
3)
else
(if i.val < 93 then
3
else
(if i.val < 94 then
3
else
3)))
else
(if i.val < 98 then
(if i.val < 96 then
3
else
(if i.val < 97 then
3
else
3))
else
(if i.val < 99 then
3
else
(if i.val < 100 then
3
else
3))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
3
else
3)
else
(if i.val < 104 then
3
else
(if i.val < 105 then
3
else
3)))
else
(if i.val < 109 then
(if i.val < 107 then
3
else
(if i.val < 108 then
3
else
3))
else
(if i.val < 110 then
3
else
(if i.val < 111 then
3
else
3)))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
3
else
3)
else
(if i.val < 115 then
3
else
(if i.val < 116 then
3
else
3)))
else
(if i.val < 120 then
(if i.val < 118 then
3
else
(if i.val < 119 then
3
else
3))
else
(if i.val < 121 then
3
else
(if i.val < 122 then
3
else
3))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
3
else
(if i.val < 125 then
3
else
3))
else
(if i.val < 127 then
3
else
(if i.val < 128 then
3
else
3)))
else
(if i.val < 132 then
(if i.val < 130 then
3
else
(if i.val < 131 then
3
else
3))
else
(if i.val < 133 then
3
else
(if i.val < 134 then
3
else
3))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
3
else
3)
else
(if i.val < 138 then
3
else
(if i.val < 139 then
3
else
3)))
else
(if i.val < 143 then
(if i.val < 141 then
3
else
(if i.val < 142 then
3
else
3))
else
(if i.val < 144 then
3
else
(if i.val < 145 then
3
else
3))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
3
else
3)
else
(if i.val < 149 then
3
else
(if i.val < 150 then
3
else
3)))
else
(if i.val < 154 then
(if i.val < 152 then
3
else
(if i.val < 153 then
3
else
3))
else
(if i.val < 155 then
3
else
(if i.val < 156 then
3
else
3)))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
3
else
3)
else
(if i.val < 160 then
3
else
(if i.val < 161 then
3
else
3)))
else
(if i.val < 165 then
(if i.val < 163 then
3
else
(if i.val < 164 then
3
else
3))
else
(if i.val < 166 then
3
else
(if i.val < 167 then
3
else
3))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
3
else
(if i.val < 170 then
3
else
3))
else
(if i.val < 172 then
3
else
(if i.val < 173 then
3
else
3)))
else
(if i.val < 177 then
(if i.val < 175 then
3
else
(if i.val < 176 then
3
else
3))
else
(if i.val < 178 then
3
else
(if i.val < 179 then
3
else
3))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
3
else
3)
else
(if i.val < 183 then
3
else
(if i.val < 184 then
3
else
3)))
else
(if i.val < 188 then
(if i.val < 186 then
3
else
(if i.val < 187 then
3
else
3))
else
(if i.val < 189 then
3
else
(if i.val < 190 then
3
else
3))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
3
else
3)
else
(if i.val < 194 then
3
else
(if i.val < 195 then
3
else
3)))
else
(if i.val < 199 then
(if i.val < 197 then
3
else
(if i.val < 198 then
3
else
3))
else
(if i.val < 200 then
3
else
(if i.val < 201 then
3
else
3)))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
3
else
3)
else
(if i.val < 205 then
3
else
(if i.val < 206 then
3
else
3)))
else
(if i.val < 210 then
(if i.val < 208 then
3
else
(if i.val < 209 then
3
else
3))
else
(if i.val < 211 then
3
else
(if i.val < 212 then
3
else
3))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
3
else
(if i.val < 215 then
3
else
3))
else
(if i.val < 217 then
3
else
(if i.val < 218 then
3
else
3)))
else
(if i.val < 222 then
(if i.val < 220 then
3
else
(if i.val < 221 then
3
else
3))
else
(if i.val < 223 then
3
else
(if i.val < 224 then
3
else
3))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
3
else
3)
else
(if i.val < 228 then
3
else
(if i.val < 229 then
3
else
3)))
else
(if i.val < 233 then
(if i.val < 231 then
3
else
(if i.val < 232 then
3
else
3))
else
(if i.val < 234 then
3
else
(if i.val < 235 then
3
else
3))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
3
else
3)
else
(if i.val < 239 then
3
else
(if i.val < 240 then
3
else
3)))
else
(if i.val < 244 then
(if i.val < 242 then
3
else
(if i.val < 243 then
3
else
3))
else
(if i.val < 245 then
3
else
(if i.val < 246 then
3
else
3)))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
3
else
3)
else
(if i.val < 250 then
3
else
(if i.val < 251 then
3
else
3)))
else
(if i.val < 255 then
(if i.val < 253 then
3
else
(if i.val < 254 then
3
else
3))
else
(if i.val < 256 then
3
else
(if i.val < 257 then
3
else
3))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
3
else
(if i.val < 260 then
3
else
3))
else
(if i.val < 262 then
3
else
(if i.val < 263 then
3
else
3)))
else
(if i.val < 267 then
(if i.val < 265 then
3
else
(if i.val < 266 then
3
else
3))
else
(if i.val < 268 then
3
else
(if i.val < 269 then
3
else
3)))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
3
else
3)
else
(if i.val < 273 then
3
else
(if i.val < 274 then
3
else
3)))
else
(if i.val < 278 then
(if i.val < 276 then
3
else
(if i.val < 277 then
3
else
3))
else
(if i.val < 279 then
3
else
(if i.val < 280 then
3
else
3))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
3
else
3)
else
(if i.val < 284 then
3
else
(if i.val < 285 then
3
else
3)))
else
(if i.val < 289 then
(if i.val < 287 then
3
else
(if i.val < 288 then
3
else
3))
else
(if i.val < 290 then
3
else
(if i.val < 291 then
3
else
3)))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
3
else
3)
else
(if i.val < 295 then
3
else
(if i.val < 296 then
3
else
3)))
else
(if i.val < 300 then
(if i.val < 298 then
3
else
(if i.val < 299 then
3
else
3))
else
(if i.val < 301 then
3
else
(if i.val < 302 then
3
else
3))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
3
else
(if i.val < 305 then
3
else
3))
else
(if i.val < 307 then
3
else
(if i.val < 308 then
3
else
3)))
else
(if i.val < 312 then
(if i.val < 310 then
3
else
(if i.val < 311 then
3
else
3))
else
(if i.val < 313 then
3
else
(if i.val < 314 then
3
else
3))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
3
else
3)
else
(if i.val < 318 then
3
else
(if i.val < 319 then
3
else
3)))
else
(if i.val < 323 then
(if i.val < 321 then
3
else
(if i.val < 322 then
3
else
3))
else
(if i.val < 324 then
3
else
(if i.val < 325 then
3
else
3))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
3
else
3)
else
(if i.val < 329 then
3
else
(if i.val < 330 then
3
else
3)))
else
(if i.val < 334 then
(if i.val < 332 then
3
else
(if i.val < 333 then
3
else
3))
else
(if i.val < 335 then
3
else
(if i.val < 336 then
3
else
3)))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
3
else
3)
else
(if i.val < 340 then
3
else
(if i.val < 341 then
3
else
3)))
else
(if i.val < 345 then
(if i.val < 343 then
3
else
(if i.val < 344 then
3
else
3))
else
(if i.val < 346 then
3
else
(if i.val < 347 then
3
else
3))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
3
else
(if i.val < 350 then
3
else
3))
else
(if i.val < 352 then
3
else
(if i.val < 353 then
3
else
3)))
else
(if i.val < 357 then
(if i.val < 355 then
3
else
(if i.val < 356 then
3
else
3))
else
(if i.val < 358 then
3
else
(if i.val < 359 then
3
else
3)))))))))

def g32p_row06_cosetCycleNodes0 : Fin 360 → List ℕ :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
[0, 634, 857]
else
[1, 930, 29])
else
(if i.val < 3 then
[2, 872, 493]
else
(if i.val < 4 then
[3, 900, 361]
else
[4, 197, 447])))
else
(if i.val < 8 then
(if i.val < 6 then
[5, 362, 579]
else
(if i.val < 7 then
[6, 423, 57]
else
[7, 1052, 80]))
else
(if i.val < 9 then
[8, 369, 646]
else
(if i.val < 10 then
[9, 501, 92]
else
[10, 374, 721]))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
[11, 415, 540]
else
[12, 446, 116])
else
(if i.val < 14 then
[13, 437, 618]
else
(if i.val < 15 then
[14, 1031, 651]
else
[15, 407, 644])))
else
(if i.val < 19 then
(if i.val < 17 then
[16, 387, 683]
else
(if i.val < 18 then
[17, 1045, 633]
else
[18, 342, 690]))
else
(if i.val < 20 then
[19, 607, 953]
else
(if i.val < 21 then
[20, 658, 868]
else
[21, 568, 167])))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
[22, 565, 211]
else
[23, 659, 204])
else
(if i.val < 25 then
[24, 779, 859]
else
(if i.val < 26 then
[25, 663, 185]
else
[26, 544, 144])))
else
(if i.val < 30 then
(if i.val < 28 then
[27, 730, 194]
else
(if i.val < 29 then
[28, 621, 293]
else
[30, 84, 206]))
else
(if i.val < 31 then
[31, 583, 213]
else
(if i.val < 32 then
[32, 541, 258]
else
[33, 671, 219]))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
[34, 548, 147]
else
(if i.val < 35 then
[35, 722, 226]
else
[36, 599, 795]))
else
(if i.val < 37 then
[37, 81, 198]
else
(if i.val < 38 then
[38, 707, 860]
else
[39, 602, 200])))
else
(if i.val < 42 then
(if i.val < 40 then
[40, 741, 909]
else
(if i.val < 41 then
[41, 120, 265]
else
[42, 1079, 210]))
else
(if i.val < 43 then
[43, 735, 259]
else
(if i.val < 44 then
[44, 666, 922]
else
[45, 106, 271]))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
[46, 83, 244]
else
[47, 694, 227])
else
(if i.val < 48 then
[48, 1075, 910]
else
(if i.val < 49 then
[49, 592, 230]
else
[50, 723, 164])))
else
(if i.val < 53 then
(if i.val < 51 then
[51, 609, 807]
else
(if i.val < 52 then
[52, 682, 248]
else
[53, 127, 276]))
else
(if i.val < 54 then
[54, 606, 887]
else
(if i.val < 55 then
[55, 811, 450]
else
[56, 282, 1000]))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
[58, 260, 389]
else
[59, 881, 368])
else
(if i.val < 59 then
[60, 171, 365]
else
(if i.val < 60 then
[61, 142, 363]
else
[62, 228, 1005])))
else
(if i.val < 64 then
(if i.val < 62 then
[63, 876, 324]
else
(if i.val < 63 then
[64, 806, 309]
else
[65, 873, 359]))
else
(if i.val < 65 then
[66, 941, 1028]
else
(if i.val < 66 then
[67, 193, 438]
else
[68, 797, 987])))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
[69, 907, 427]
else
[70, 173, 370])
else
(if i.val < 70 then
[71, 234, 426]
else
(if i.val < 71 then
[72, 159, 410]
else
[73, 946, 393])))
else
(if i.val < 75 then
(if i.val < 73 then
[74, 804, 357]
else
(if i.val < 74 then
[75, 892, 322]
else
[76, 146, 477]))
else
(if i.val < 76 then
[77, 891, 412]
else
(if i.val < 77 then
[78, 217, 403]
else
[79, 827, 358]))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
[82, 899, 499]
else
(if i.val < 80 then
[85, 181, 424]
else
[86, 145, 334]))
else
(if i.val < 82 then
[87, 814, 333]
else
(if i.val < 83 then
[88, 846, 1056]
else
[89, 810, 377])))
else
(if i.val < 87 then
(if i.val < 85 then
[90, 268, 349]
else
(if i.val < 86 then
[91, 152, 321]
else
[93, 222, 327]))
else
(if i.val < 88 then
[94, 813, 454]
else
(if i.val < 89 then
[95, 796, 396]
else
[96, 883, 457])))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
[97, 823, 425]
else
[98, 858, 328])
else
(if i.val < 93 then
[99, 243, 475]
else
(if i.val < 94 then
[100, 979, 332]
else
[101, 929, 420])))
else
(if i.val < 98 then
(if i.val < 96 then
[102, 208, 316]
else
(if i.val < 97 then
[103, 233, 385]
else
[104, 221, 314]))
else
(if i.val < 99 then
[105, 981, 1046]
else
(if i.val < 100 then
[107, 866, 346]
else
[108, 207, 382]))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
[109, 864, 391]
else
[110, 180, 482])
else
(if i.val < 104 then
[111, 215, 507]
else
(if i.val < 105 then
[112, 255, 323]
else
[113, 963, 496])))
else
(if i.val < 109 then
(if i.val < 107 then
[114, 156, 461]
else
(if i.val < 108 then
[115, 195, 408]
else
[117, 964, 417]))
else
(if i.val < 110 then
[118, 251, 435]
else
(if i.val < 111 then
[119, 178, 433]
else
[121, 231, 459])))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
[122, 983, 526]
else
[123, 877, 432])
else
(if i.val < 115 then
[124, 817, 301]
else
(if i.val < 116 then
[125, 236, 991]
else
[126, 914, 383])))
else
(if i.val < 120 then
(if i.val < 118 then
[128, 880, 1042]
else
(if i.val < 119 then
[129, 179, 351]
else
[130, 155, 465]))
else
(if i.val < 121 then
[131, 919, 529]
else
(if i.val < 122 then
[132, 918, 397]
else
[133, 190, 441]))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
[134, 847, 490]
else
(if i.val < 125 then
[135, 257, 440]
else
[136, 965, 326]))
else
(if i.val < 127 then
[137, 188, 398]
else
(if i.val < 128 then
[138, 318, 594]
else
[139, 379, 652])))
else
(if i.val < 132 then
(if i.val < 130 then
[140, 300, 549]
else
(if i.val < 131 then
[141, 390, 580]
else
[143, 406, 736]))
else
(if i.val < 133 then
[148, 329, 590]
else
(if i.val < 134 then
[149, 996, 665]
else
[150, 516, 738]))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
[151, 336, 696]
else
[153, 466, 626])
else
(if i.val < 138 then
[154, 307, 598]
else
(if i.val < 139 then
[157, 510, 790]
else
[158, 386, 673])))
else
(if i.val < 143 then
(if i.val < 141 then
[160, 995, 593]
else
(if i.val < 142 then
[161, 1050, 754]
else
[162, 536, 667]))
else
(if i.val < 144 then
[163, 392, 699]
else
(if i.val < 145 then
[165, 373, 628]
else
[166, 399, 630]))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
[168, 1040, 782]
else
[169, 997, 617])
else
(if i.val < 149 then
[170, 303, 542]
else
(if i.val < 150 then
[172, 296, 662]
else
[174, 366, 664])))
else
(if i.val < 154 then
(if i.val < 152 then
[175, 498, 539]
else
(if i.val < 153 then
[176, 468, 627]
else
[177, 500, 674]))
else
(if i.val < 155 then
[182, 347, 632]
else
(if i.val < 156 then
[183, 311, 563]
else
[184, 297, 551])))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
[186, 428, 1068]
else
[187, 531, 550])
else
(if i.val < 160 then
[189, 471, 687]
else
(if i.val < 161 then
[191, 310, 743]
else
[192, 1043, 705])))
else
(if i.val < 165 then
(if i.val < 163 then
[196, 384, 641]
else
(if i.val < 164 then
[199, 401, 713]
else
[201, 1016, 601]))
else
(if i.val < 166 then
[202, 421, 595]
else
(if i.val < 167 then
[203, 400, 739]
else
[205, 422, 655]))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
[209, 312, 788]
else
(if i.val < 170 then
[212, 317, 547]
else
[214, 1034, 698]))
else
(if i.val < 172 then
[216, 517, 742]
else
(if i.val < 173 then
[218, 515, 629]
else
[220, 411, 703])))
else
(if i.val < 177 then
(if i.val < 175 then
[223, 356, 591]
else
(if i.val < 176 then
[224, 298, 570]
else
[225, 402, 584]))
else
(if i.val < 178 then
[229, 452, 619]
else
(if i.val < 179 then
[232, 1047, 612]
else
[235, 451, 639]))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
[237, 355, 692]
else
[238, 535, 711])
else
(if i.val < 183 then
[239, 445, 693]
else
(if i.val < 184 then
[240, 1063, 745]
else
[241, 469, 747])))
else
(if i.val < 188 then
(if i.val < 186 then
[242, 331, 561]
else
(if i.val < 187 then
[245, 1058, 773]
else
[246, 509, 670]))
else
(if i.val < 189 then
[247, 522, 622]
else
(if i.val < 190 then
[249, 521, 640]
else
[250, 354, 624]))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
[252, 341, 616]
else
[253, 442, 750])
else
(if i.val < 194 then
[254, 530, 760]
else
(if i.val < 195 then
[256, 1015, 732]
else
[261, 443, 700])))
else
(if i.val < 199 then
(if i.val < 197 then
[262, 1037, 714]
else
(if i.val < 198 then
[263, 463, 752]
else
[264, 1064, 600]))
else
(if i.val < 200 then
[266, 533, 657]
else
(if i.val < 201 then
[267, 414, 575]
else
[269, 504, 597])))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
[270, 483, 734]
else
[272, 1060, 562])
else
(if i.val < 205 then
[273, 988, 555]
else
(if i.val < 206 then
[274, 344, 718]
else
[275, 1051, 647])))
else
(if i.val < 210 then
(if i.val < 208 then
[277, 330, 737]
else
(if i.val < 209 then
[278, 993, 748]
else
[279, 489, 701]))
else
(if i.val < 211 then
[280, 448, 740]
else
(if i.val < 212 then
[281, 506, 615]
else
[283, 340, 702]))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
[284, 1035, 635]
else
(if i.val < 215 then
[285, 1039, 757]
else
[286, 472, 775]))
else
(if i.val < 217 then
[287, 405, 543]
else
(if i.val < 218 then
[288, 1021, 589]
else
[289, 348, 685])))
else
(if i.val < 222 then
(if i.val < 220 then
[290, 481, 574]
else
(if i.val < 221 then
[291, 350, 763]
else
[292, 352, 686]))
else
(if i.val < 223 then
[294, 1055, 688]
else
(if i.val < 224 then
[295, 648, 925]
else
[299, 537, 816]))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
[302, 645, 888]
else
[304, 709, 937])
else
(if i.val < 228 then
[305, 776, 904]
else
(if i.val < 229 then
[306, 636, 853]
else
[308, 656, 949])))
else
(if i.val < 233 then
(if i.val < 231 then
[313, 613, 870]
else
(if i.val < 232 then
[315, 578, 856]
else
[319, 586, 861]))
else
(if i.val < 234 then
[320, 697, 869]
else
(if i.val < 235 then
[325, 559, 944]
else
[335, 1066, 878]))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
[337, 556, 865]
else
[338, 608, 982])
else
(if i.val < 239 then
[339, 678, 926]
else
(if i.val < 240 then
[343, 1077, 879]
else
[345, 637, 802])))
else
(if i.val < 244 then
(if i.val < 242 then
[353, 767, 977]
else
(if i.val < 243 then
[360, 623, 934]
else
[364, 725, 913]))
else
(if i.val < 245 then
[367, 660, 917]
else
(if i.val < 246 then
[371, 538, 848]
else
[372, 689, 957])))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
[375, 758, 898]
else
[376, 643, 820])
else
(if i.val < 250 then
[378, 653, 897]
else
(if i.val < 251 then
[380, 605, 939]
else
[381, 588, 959])))
else
(if i.val < 255 then
(if i.val < 253 then
[388, 552, 906]
else
(if i.val < 254 then
[394, 638, 837]
else
[395, 610, 927]))
else
(if i.val < 256 then
[404, 715, 850]
else
(if i.val < 257 then
[409, 704, 961]
else
[413, 712, 844]))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
[416, 566, 833]
else
(if i.val < 260 then
[418, 668, 874]
else
[419, 710, 960]))
else
(if i.val < 262 then
[429, 733, 818]
else
(if i.val < 263 then
[430, 785, 819]
else
[431, 582, 896])))
else
(if i.val < 267 then
(if i.val < 265 then
[434, 553, 971]
else
(if i.val < 266 then
[436, 642, 867]
else
[439, 746, 828]))
else
(if i.val < 268 then
[444, 728, 836]
else
(if i.val < 269 then
[449, 603, 798]
else
[453, 573, 956])))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
[455, 787, 935]
else
[456, 769, 928])
else
(if i.val < 273 then
[458, 680, 958]
else
(if i.val < 274 then
[460, 545, 947]
else
[462, 778, 973])))
else
(if i.val < 278 then
(if i.val < 276 then
[464, 792, 838]
else
(if i.val < 277 then
[467, 1078, 895]
else
[470, 679, 841]))
else
(if i.val < 279 then
[473, 585, 843]
else
(if i.val < 280 then
[474, 793, 912]
else
[476, 777, 809]))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
[478, 765, 968]
else
[479, 1073, 826])
else
(if i.val < 284 then
[480, 1065, 822]
else
(if i.val < 285 then
[484, 759, 942]
else
[485, 677, 851])))
else
(if i.val < 289 then
(if i.val < 287 then
[486, 766, 829]
else
(if i.val < 288 then
[487, 569, 902]
else
[488, 611, 905]))
else
(if i.val < 290 then
[491, 756, 924]
else
(if i.val < 291 then
[492, 557, 950]
else
[494, 560, 803])))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
[495, 581, 812]
else
[497, 1076, 885])
else
(if i.val < 295 then
[502, 726, 800]
else
(if i.val < 296 then
[503, 789, 974]
else
[505, 1070, 972])))
else
(if i.val < 300 then
(if i.val < 298 then
[508, 753, 951]
else
(if i.val < 299 then
[511, 576, 911]
else
[512, 706, 821]))
else
(if i.val < 301 then
[513, 791, 799]
else
(if i.val < 302 then
[514, 761, 970]
else
[518, 650, 931]))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
[519, 783, 893]
else
(if i.val < 305 then
[520, 794, 875]
else
[523, 768, 908]))
else
(if i.val < 307 then
[524, 567, 955]
else
(if i.val < 308 then
[525, 708, 840]
else
[527, 564, 936])))
else
(if i.val < 312 then
(if i.val < 310 then
[528, 654, 978]
else
(if i.val < 311 then
[532, 781, 976]
else
[534, 1067, 832]))
else
(if i.val < 313 then
[546, 815, 992]
else
(if i.val < 314 then
[554, 808, 1011]
else
[558, 830, 1010]))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
[571, 845, 1022]
else
[572, 855, 1049])
else
(if i.val < 318 then
[577, 834, 1025]
else
(if i.val < 319 then
[587, 954, 1032]
else
[596, 933, 984])))
else
(if i.val < 323 then
(if i.val < 321 then
[604, 882, 1048]
else
(if i.val < 322 then
[614, 852, 999]
else
[620, 871, 1044]))
else
(if i.val < 324 then
[625, 962, 1062]
else
(if i.val < 325 then
[631, 952, 1059]
else
[649, 916, 1018]))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
[661, 932, 1036]
else
[669, 915, 1027])
else
(if i.val < 329 then
[672, 943, 1006]
else
(if i.val < 330 then
[675, 889, 1014]
else
[676, 903, 989])))
else
(if i.val < 334 then
(if i.val < 332 then
[681, 886, 1020]
else
(if i.val < 333 then
[684, 825, 985]
else
[691, 831, 994]))
else
(if i.val < 335 then
[695, 862, 1053]
else
(if i.val < 336 then
[716, 835, 1057]
else
[717, 967, 1003])))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
[719, 901, 1061]
else
[720, 805, 1029])
else
(if i.val < 340 then
[724, 890, 1002]
else
(if i.val < 341 then
[727, 863, 1017]
else
[729, 849, 1023])))
else
(if i.val < 345 then
(if i.val < 343 then
[731, 824, 1041]
else
(if i.val < 344 then
[744, 940, 1007]
else
[749, 923, 1004]))
else
(if i.val < 346 then
[751, 975, 1009]
else
(if i.val < 347 then
[755, 966, 1030]
else
[762, 980, 1038]))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
[764, 938, 1019]
else
(if i.val < 350 then
[770, 801, 998]
else
[771, 945, 1026]))
else
(if i.val < 352 then
[772, 839, 990]
else
(if i.val < 353 then
[774, 920, 1033]
else
[780, 842, 1008])))
else
(if i.val < 357 then
(if i.val < 355 then
[784, 884, 986]
else
(if i.val < 356 then
[786, 854, 1012]
else
[894, 1001, 1069]))
else
(if i.val < 358 then
[921, 1013, 1072]
else
(if i.val < 359 then
[948, 1054, 1074]
else
[969, 1024, 1071])))))))))

def g32p_row06_cosetCycles0 : List (List ℕ) :=
  List.ofFn g32p_row06_cosetCycleNodes0

def g32p_row06_cosetMonodromies0 : Fin 360 → Fin 144 :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
0
else
(if i.val < 4 then
0
else
0)))
else
(if i.val < 8 then
(if i.val < 6 then
0
else
(if i.val < 7 then
0
else
0))
else
(if i.val < 9 then
0
else
(if i.val < 10 then
0
else
0))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
0
else
0)
else
(if i.val < 14 then
0
else
(if i.val < 15 then
0
else
0)))
else
(if i.val < 19 then
(if i.val < 17 then
0
else
(if i.val < 18 then
0
else
0))
else
(if i.val < 20 then
0
else
(if i.val < 21 then
0
else
0)))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
0
else
0)
else
(if i.val < 25 then
0
else
(if i.val < 26 then
0
else
0)))
else
(if i.val < 30 then
(if i.val < 28 then
0
else
(if i.val < 29 then
0
else
0))
else
(if i.val < 31 then
0
else
(if i.val < 32 then
0
else
0))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
0
else
(if i.val < 35 then
0
else
0))
else
(if i.val < 37 then
0
else
(if i.val < 38 then
0
else
0)))
else
(if i.val < 42 then
(if i.val < 40 then
0
else
(if i.val < 41 then
0
else
0))
else
(if i.val < 43 then
0
else
(if i.val < 44 then
0
else
0))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
0
else
0)
else
(if i.val < 48 then
0
else
(if i.val < 49 then
0
else
0)))
else
(if i.val < 53 then
(if i.val < 51 then
0
else
(if i.val < 52 then
0
else
0))
else
(if i.val < 54 then
0
else
(if i.val < 55 then
0
else
0))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
0
else
0)
else
(if i.val < 59 then
0
else
(if i.val < 60 then
0
else
0)))
else
(if i.val < 64 then
(if i.val < 62 then
0
else
(if i.val < 63 then
0
else
0))
else
(if i.val < 65 then
0
else
(if i.val < 66 then
0
else
0)))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
0
else
0)
else
(if i.val < 70 then
0
else
(if i.val < 71 then
0
else
0)))
else
(if i.val < 75 then
(if i.val < 73 then
0
else
(if i.val < 74 then
0
else
0))
else
(if i.val < 76 then
0
else
(if i.val < 77 then
0
else
0))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
0
else
(if i.val < 80 then
0
else
0))
else
(if i.val < 82 then
0
else
(if i.val < 83 then
0
else
0)))
else
(if i.val < 87 then
(if i.val < 85 then
0
else
(if i.val < 86 then
0
else
0))
else
(if i.val < 88 then
0
else
(if i.val < 89 then
0
else
0)))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
0
else
0)
else
(if i.val < 93 then
0
else
(if i.val < 94 then
0
else
0)))
else
(if i.val < 98 then
(if i.val < 96 then
0
else
(if i.val < 97 then
0
else
0))
else
(if i.val < 99 then
0
else
(if i.val < 100 then
0
else
0))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
0
else
0)
else
(if i.val < 104 then
0
else
(if i.val < 105 then
0
else
0)))
else
(if i.val < 109 then
(if i.val < 107 then
0
else
(if i.val < 108 then
0
else
0))
else
(if i.val < 110 then
0
else
(if i.val < 111 then
0
else
0)))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
0
else
0)
else
(if i.val < 115 then
0
else
(if i.val < 116 then
0
else
0)))
else
(if i.val < 120 then
(if i.val < 118 then
0
else
(if i.val < 119 then
0
else
0))
else
(if i.val < 121 then
0
else
(if i.val < 122 then
0
else
0))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
0
else
(if i.val < 125 then
0
else
0))
else
(if i.val < 127 then
0
else
(if i.val < 128 then
0
else
0)))
else
(if i.val < 132 then
(if i.val < 130 then
0
else
(if i.val < 131 then
0
else
0))
else
(if i.val < 133 then
0
else
(if i.val < 134 then
0
else
0))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
0
else
0)
else
(if i.val < 138 then
0
else
(if i.val < 139 then
0
else
0)))
else
(if i.val < 143 then
(if i.val < 141 then
0
else
(if i.val < 142 then
0
else
0))
else
(if i.val < 144 then
0
else
(if i.val < 145 then
0
else
0))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
0
else
0)
else
(if i.val < 149 then
0
else
(if i.val < 150 then
0
else
0)))
else
(if i.val < 154 then
(if i.val < 152 then
0
else
(if i.val < 153 then
0
else
0))
else
(if i.val < 155 then
0
else
(if i.val < 156 then
0
else
0)))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
0
else
0)
else
(if i.val < 160 then
0
else
(if i.val < 161 then
0
else
0)))
else
(if i.val < 165 then
(if i.val < 163 then
0
else
(if i.val < 164 then
0
else
0))
else
(if i.val < 166 then
0
else
(if i.val < 167 then
0
else
0))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
0
else
(if i.val < 170 then
0
else
0))
else
(if i.val < 172 then
0
else
(if i.val < 173 then
0
else
0)))
else
(if i.val < 177 then
(if i.val < 175 then
0
else
(if i.val < 176 then
0
else
0))
else
(if i.val < 178 then
0
else
(if i.val < 179 then
0
else
0))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
0
else
0)
else
(if i.val < 183 then
0
else
(if i.val < 184 then
0
else
0)))
else
(if i.val < 188 then
(if i.val < 186 then
0
else
(if i.val < 187 then
0
else
0))
else
(if i.val < 189 then
0
else
(if i.val < 190 then
0
else
0))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
0
else
0)
else
(if i.val < 194 then
0
else
(if i.val < 195 then
0
else
0)))
else
(if i.val < 199 then
(if i.val < 197 then
0
else
(if i.val < 198 then
0
else
0))
else
(if i.val < 200 then
0
else
(if i.val < 201 then
0
else
0)))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
0
else
0)
else
(if i.val < 205 then
0
else
(if i.val < 206 then
0
else
0)))
else
(if i.val < 210 then
(if i.val < 208 then
0
else
(if i.val < 209 then
0
else
0))
else
(if i.val < 211 then
0
else
(if i.val < 212 then
0
else
0))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
0
else
(if i.val < 215 then
0
else
0))
else
(if i.val < 217 then
0
else
(if i.val < 218 then
0
else
0)))
else
(if i.val < 222 then
(if i.val < 220 then
0
else
(if i.val < 221 then
0
else
0))
else
(if i.val < 223 then
0
else
(if i.val < 224 then
0
else
0))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
0
else
0)
else
(if i.val < 228 then
0
else
(if i.val < 229 then
0
else
0)))
else
(if i.val < 233 then
(if i.val < 231 then
0
else
(if i.val < 232 then
0
else
0))
else
(if i.val < 234 then
0
else
(if i.val < 235 then
0
else
0))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
(if i.val < 240 then
0
else
0)))
else
(if i.val < 244 then
(if i.val < 242 then
0
else
(if i.val < 243 then
0
else
0))
else
(if i.val < 245 then
0
else
(if i.val < 246 then
0
else
0)))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
0
else
0)
else
(if i.val < 250 then
0
else
(if i.val < 251 then
0
else
0)))
else
(if i.val < 255 then
(if i.val < 253 then
0
else
(if i.val < 254 then
0
else
0))
else
(if i.val < 256 then
0
else
(if i.val < 257 then
0
else
0))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
0
else
(if i.val < 260 then
0
else
0))
else
(if i.val < 262 then
0
else
(if i.val < 263 then
0
else
0)))
else
(if i.val < 267 then
(if i.val < 265 then
0
else
(if i.val < 266 then
0
else
0))
else
(if i.val < 268 then
0
else
(if i.val < 269 then
0
else
0)))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
0
else
0)
else
(if i.val < 273 then
0
else
(if i.val < 274 then
0
else
0)))
else
(if i.val < 278 then
(if i.val < 276 then
0
else
(if i.val < 277 then
0
else
0))
else
(if i.val < 279 then
0
else
(if i.val < 280 then
0
else
0))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
0
else
0)
else
(if i.val < 284 then
0
else
(if i.val < 285 then
0
else
0)))
else
(if i.val < 289 then
(if i.val < 287 then
0
else
(if i.val < 288 then
0
else
0))
else
(if i.val < 290 then
0
else
(if i.val < 291 then
0
else
0)))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
0
else
0)
else
(if i.val < 295 then
0
else
(if i.val < 296 then
0
else
0)))
else
(if i.val < 300 then
(if i.val < 298 then
0
else
(if i.val < 299 then
0
else
0))
else
(if i.val < 301 then
0
else
(if i.val < 302 then
0
else
0))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
0
else
(if i.val < 305 then
0
else
0))
else
(if i.val < 307 then
0
else
(if i.val < 308 then
0
else
0)))
else
(if i.val < 312 then
(if i.val < 310 then
0
else
(if i.val < 311 then
0
else
0))
else
(if i.val < 313 then
0
else
(if i.val < 314 then
0
else
0))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
0
else
0)
else
(if i.val < 318 then
0
else
(if i.val < 319 then
0
else
0)))
else
(if i.val < 323 then
(if i.val < 321 then
0
else
(if i.val < 322 then
0
else
0))
else
(if i.val < 324 then
0
else
(if i.val < 325 then
0
else
0))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
0
else
0)
else
(if i.val < 329 then
0
else
(if i.val < 330 then
0
else
0)))
else
(if i.val < 334 then
(if i.val < 332 then
0
else
(if i.val < 333 then
0
else
0))
else
(if i.val < 335 then
0
else
(if i.val < 336 then
0
else
0)))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
0
else
0)
else
(if i.val < 340 then
0
else
(if i.val < 341 then
0
else
0)))
else
(if i.val < 345 then
(if i.val < 343 then
0
else
(if i.val < 344 then
0
else
0))
else
(if i.val < 346 then
0
else
(if i.val < 347 then
0
else
0))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
0
else
(if i.val < 350 then
0
else
0))
else
(if i.val < 352 then
0
else
(if i.val < 353 then
0
else
0)))
else
(if i.val < 357 then
(if i.val < 355 then
0
else
(if i.val < 356 then
0
else
0))
else
(if i.val < 358 then
0
else
(if i.val < 359 then
0
else
0)))))))))

def g32p_row06_cosetExponents0 : Fin 360 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 3 then
Multiplicative.ofAdd 0
else
(if i.val < 4 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 8 then
(if i.val < 6 then
Multiplicative.ofAdd 0
else
(if i.val < 7 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 9 then
Multiplicative.ofAdd 0
else
(if i.val < 10 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 14 then
Multiplicative.ofAdd 0
else
(if i.val < 15 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 19 then
(if i.val < 17 then
Multiplicative.ofAdd 0
else
(if i.val < 18 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 20 then
Multiplicative.ofAdd 0
else
(if i.val < 21 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 25 then
Multiplicative.ofAdd 0
else
(if i.val < 26 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 30 then
(if i.val < 28 then
Multiplicative.ofAdd 0
else
(if i.val < 29 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 31 then
Multiplicative.ofAdd 0
else
(if i.val < 32 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
Multiplicative.ofAdd 0
else
(if i.val < 35 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 37 then
Multiplicative.ofAdd 0
else
(if i.val < 38 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 42 then
(if i.val < 40 then
Multiplicative.ofAdd 0
else
(if i.val < 41 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 43 then
Multiplicative.ofAdd 0
else
(if i.val < 44 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 48 then
Multiplicative.ofAdd 0
else
(if i.val < 49 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 53 then
(if i.val < 51 then
Multiplicative.ofAdd 0
else
(if i.val < 52 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 54 then
Multiplicative.ofAdd 0
else
(if i.val < 55 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 59 then
Multiplicative.ofAdd 0
else
(if i.val < 60 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 64 then
(if i.val < 62 then
Multiplicative.ofAdd 0
else
(if i.val < 63 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 65 then
Multiplicative.ofAdd 0
else
(if i.val < 66 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 70 then
Multiplicative.ofAdd 0
else
(if i.val < 71 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 75 then
(if i.val < 73 then
Multiplicative.ofAdd 0
else
(if i.val < 74 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 76 then
Multiplicative.ofAdd 0
else
(if i.val < 77 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
Multiplicative.ofAdd 0
else
(if i.val < 80 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 82 then
Multiplicative.ofAdd 0
else
(if i.val < 83 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 87 then
(if i.val < 85 then
Multiplicative.ofAdd 0
else
(if i.val < 86 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 88 then
Multiplicative.ofAdd 0
else
(if i.val < 89 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 93 then
Multiplicative.ofAdd 0
else
(if i.val < 94 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 98 then
(if i.val < 96 then
Multiplicative.ofAdd 0
else
(if i.val < 97 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 99 then
Multiplicative.ofAdd 0
else
(if i.val < 100 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 104 then
Multiplicative.ofAdd 0
else
(if i.val < 105 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 109 then
(if i.val < 107 then
Multiplicative.ofAdd 0
else
(if i.val < 108 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 110 then
Multiplicative.ofAdd 0
else
(if i.val < 111 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 115 then
Multiplicative.ofAdd 0
else
(if i.val < 116 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 120 then
(if i.val < 118 then
Multiplicative.ofAdd 0
else
(if i.val < 119 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 121 then
Multiplicative.ofAdd 0
else
(if i.val < 122 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
Multiplicative.ofAdd 0
else
(if i.val < 125 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 127 then
Multiplicative.ofAdd 0
else
(if i.val < 128 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 132 then
(if i.val < 130 then
Multiplicative.ofAdd 0
else
(if i.val < 131 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 133 then
Multiplicative.ofAdd 0
else
(if i.val < 134 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 138 then
Multiplicative.ofAdd 0
else
(if i.val < 139 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 143 then
(if i.val < 141 then
Multiplicative.ofAdd 0
else
(if i.val < 142 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 144 then
Multiplicative.ofAdd 0
else
(if i.val < 145 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 149 then
Multiplicative.ofAdd 0
else
(if i.val < 150 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 154 then
(if i.val < 152 then
Multiplicative.ofAdd 0
else
(if i.val < 153 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 155 then
Multiplicative.ofAdd 0
else
(if i.val < 156 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 160 then
Multiplicative.ofAdd 0
else
(if i.val < 161 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 165 then
(if i.val < 163 then
Multiplicative.ofAdd 0
else
(if i.val < 164 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 166 then
Multiplicative.ofAdd 0
else
(if i.val < 167 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
Multiplicative.ofAdd 0
else
(if i.val < 170 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 172 then
Multiplicative.ofAdd 0
else
(if i.val < 173 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 177 then
(if i.val < 175 then
Multiplicative.ofAdd 0
else
(if i.val < 176 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 178 then
Multiplicative.ofAdd 0
else
(if i.val < 179 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 183 then
Multiplicative.ofAdd 0
else
(if i.val < 184 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 188 then
(if i.val < 186 then
Multiplicative.ofAdd 0
else
(if i.val < 187 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 189 then
Multiplicative.ofAdd 0
else
(if i.val < 190 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 194 then
Multiplicative.ofAdd 0
else
(if i.val < 195 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 199 then
(if i.val < 197 then
Multiplicative.ofAdd 0
else
(if i.val < 198 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 200 then
Multiplicative.ofAdd 0
else
(if i.val < 201 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 205 then
Multiplicative.ofAdd 0
else
(if i.val < 206 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 210 then
(if i.val < 208 then
Multiplicative.ofAdd 0
else
(if i.val < 209 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 211 then
Multiplicative.ofAdd 0
else
(if i.val < 212 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
Multiplicative.ofAdd 0
else
(if i.val < 215 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 217 then
Multiplicative.ofAdd 0
else
(if i.val < 218 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 222 then
(if i.val < 220 then
Multiplicative.ofAdd 0
else
(if i.val < 221 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 223 then
Multiplicative.ofAdd 0
else
(if i.val < 224 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 228 then
Multiplicative.ofAdd 0
else
(if i.val < 229 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 233 then
(if i.val < 231 then
Multiplicative.ofAdd 0
else
(if i.val < 232 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 234 then
Multiplicative.ofAdd 0
else
(if i.val < 235 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 239 then
Multiplicative.ofAdd 0
else
(if i.val < 240 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 244 then
(if i.val < 242 then
Multiplicative.ofAdd 0
else
(if i.val < 243 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 245 then
Multiplicative.ofAdd 0
else
(if i.val < 246 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 250 then
Multiplicative.ofAdd 0
else
(if i.val < 251 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 255 then
(if i.val < 253 then
Multiplicative.ofAdd 0
else
(if i.val < 254 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 256 then
Multiplicative.ofAdd 0
else
(if i.val < 257 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
Multiplicative.ofAdd 0
else
(if i.val < 260 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 262 then
Multiplicative.ofAdd 0
else
(if i.val < 263 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 267 then
(if i.val < 265 then
Multiplicative.ofAdd 0
else
(if i.val < 266 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 268 then
Multiplicative.ofAdd 0
else
(if i.val < 269 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 273 then
Multiplicative.ofAdd 0
else
(if i.val < 274 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 278 then
(if i.val < 276 then
Multiplicative.ofAdd 0
else
(if i.val < 277 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 279 then
Multiplicative.ofAdd 0
else
(if i.val < 280 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 284 then
Multiplicative.ofAdd 0
else
(if i.val < 285 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 289 then
(if i.val < 287 then
Multiplicative.ofAdd 0
else
(if i.val < 288 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 290 then
Multiplicative.ofAdd 0
else
(if i.val < 291 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 295 then
Multiplicative.ofAdd 0
else
(if i.val < 296 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 300 then
(if i.val < 298 then
Multiplicative.ofAdd 0
else
(if i.val < 299 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 301 then
Multiplicative.ofAdd 0
else
(if i.val < 302 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
Multiplicative.ofAdd 0
else
(if i.val < 305 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 307 then
Multiplicative.ofAdd 0
else
(if i.val < 308 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 312 then
(if i.val < 310 then
Multiplicative.ofAdd 0
else
(if i.val < 311 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 313 then
Multiplicative.ofAdd 0
else
(if i.val < 314 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 318 then
Multiplicative.ofAdd 0
else
(if i.val < 319 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 323 then
(if i.val < 321 then
Multiplicative.ofAdd 0
else
(if i.val < 322 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 324 then
Multiplicative.ofAdd 0
else
(if i.val < 325 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 329 then
Multiplicative.ofAdd 0
else
(if i.val < 330 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 334 then
(if i.val < 332 then
Multiplicative.ofAdd 0
else
(if i.val < 333 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 335 then
Multiplicative.ofAdd 0
else
(if i.val < 336 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 340 then
Multiplicative.ofAdd 0
else
(if i.val < 341 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 345 then
(if i.val < 343 then
Multiplicative.ofAdd 0
else
(if i.val < 344 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 346 then
Multiplicative.ofAdd 0
else
(if i.val < 347 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
Multiplicative.ofAdd 0
else
(if i.val < 350 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 352 then
Multiplicative.ofAdd 0
else
(if i.val < 353 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 357 then
(if i.val < 355 then
Multiplicative.ofAdd 0
else
(if i.val < 356 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 358 then
Multiplicative.ofAdd 0
else
(if i.val < 359 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))))

def g32p_row06_cosetLabels1 : Fin 1080 → Fin 360 :=
  fun i => (if i.val < 540 then
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
1)
else
(if i.val < 3 then
2
else
3))
else
(if i.val < 6 then
(if i.val < 5 then
4
else
5)
else
(if i.val < 7 then
1
else
6)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
7
else
8)
else
(if i.val < 11 then
9
else
10))
else
(if i.val < 14 then
(if i.val < 13 then
11
else
12)
else
(if i.val < 15 then
13
else
14))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
15
else
16)
else
(if i.val < 19 then
17
else
18))
else
(if i.val < 22 then
(if i.val < 21 then
19
else
20)
else
(if i.val < 23 then
5
else
1)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
6
else
7)
else
(if i.val < 27 then
21
else
22))
else
(if i.val < 30 then
(if i.val < 29 then
11
else
23)
else
(if i.val < 31 then
24
else
(if i.val < 32 then
25
else
26))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
27
else
28)
else
(if i.val < 36 then
9
else
29))
else
(if i.val < 39 then
(if i.val < 38 then
30
else
13)
else
(if i.val < 40 then
31
else
4)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
32
else
33)
else
(if i.val < 44 then
34
else
35))
else
(if i.val < 47 then
(if i.val < 46 then
36
else
37)
else
(if i.val < 48 then
38
else
(if i.val < 49 then
39
else
40)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
41
else
42)
else
(if i.val < 53 then
43
else
44))
else
(if i.val < 56 then
(if i.val < 55 then
45
else
18)
else
(if i.val < 57 then
8
else
46)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
47
else
48)
else
(if i.val < 61 then
12
else
28))
else
(if i.val < 64 then
(if i.val < 63 then
49
else
50)
else
(if i.val < 65 then
51
else
(if i.val < 66 then
0
else
19)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
20
else
5)
else
(if i.val < 70 then
6
else
7))
else
(if i.val < 73 then
(if i.val < 72 then
21
else
22)
else
(if i.val < 74 then
11
else
23)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
24
else
25)
else
(if i.val < 78 then
52
else
53))
else
(if i.val < 81 then
(if i.val < 80 then
54
else
55)
else
(if i.val < 82 then
56
else
(if i.val < 83 then
57
else
58)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
59
else
60)
else
(if i.val < 87 then
61
else
45))
else
(if i.val < 90 then
(if i.val < 89 then
26
else
62)
else
(if i.val < 91 then
14
else
31)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
63
else
64)
else
(if i.val < 95 then
65
else
9))
else
(if i.val < 98 then
(if i.val < 97 then
29
else
30)
else
(if i.val < 99 then
66
else
(if i.val < 100 then
67
else
68))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
69
else
70)
else
(if i.val < 104 then
71
else
72))
else
(if i.val < 107 then
(if i.val < 106 then
73
else
74)
else
(if i.val < 108 then
75
else
76)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
77
else
78)
else
(if i.val < 112 then
79
else
80))
else
(if i.val < 115 then
(if i.val < 114 then
81
else
13)
else
(if i.val < 116 then
82
else
(if i.val < 117 then
83
else
84)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
85
else
86)
else
(if i.val < 121 then
87
else
88))
else
(if i.val < 124 then
(if i.val < 123 then
89
else
90)
else
(if i.val < 125 then
91
else
92)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
93
else
41)
else
(if i.val < 129 then
94
else
95))
else
(if i.val < 132 then
(if i.val < 131 then
96
else
97)
else
(if i.val < 133 then
98
else
(if i.val < 134 then
99
else
100))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
101
else
102)
else
(if i.val < 138 then
103
else
18))
else
(if i.val < 141 then
(if i.val < 140 then
46
else
47)
else
(if i.val < 142 then
26
else
27)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
28
else
104)
else
(if i.val < 146 then
21
else
30))
else
(if i.val < 149 then
(if i.val < 148 then
105
else
106)
else
(if i.val < 150 then
107
else
108))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
109
else
72)
else
(if i.val < 154 then
110
else
111))
else
(if i.val < 157 then
(if i.val < 156 then
112
else
113)
else
(if i.val < 158 then
55
else
114)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
115
else
45)
else
(if i.val < 162 then
2
else
3))
else
(if i.val < 165 then
(if i.val < 164 then
4
else
48)
else
(if i.val < 166 then
49
else
(if i.val < 167 then
50
else
51))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
0
else
19)
else
(if i.val < 171 then
20
else
22))
else
(if i.val < 174 then
(if i.val < 173 then
23
else
24)
else
(if i.val < 175 then
25
else
52)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
53
else
54)
else
(if i.val < 179 then
56
else
57))
else
(if i.val < 182 then
(if i.val < 181 then
58
else
59)
else
(if i.val < 183 then
60
else
(if i.val < 184 then
61
else
70)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
116
else
117)
else
(if i.val < 188 then
31
else
118))
else
(if i.val < 191 then
(if i.val < 190 then
119
else
120)
else
(if i.val < 192 then
121
else
122)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
123
else
75)
else
(if i.val < 196 then
124
else
95))
else
(if i.val < 199 then
(if i.val < 198 then
125
else
126)
else
(if i.val < 200 then
127
else
(if i.val < 201 then
128
else
129)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
130
else
131)
else
(if i.val < 205 then
132
else
35))
else
(if i.val < 208 then
(if i.val < 207 then
133
else
134)
else
(if i.val < 209 then
135
else
136)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
83
else
62)
else
(if i.val < 213 then
66
else
137))
else
(if i.val < 216 then
(if i.val < 215 then
138
else
139)
else
(if i.val < 217 then
140
else
(if i.val < 218 then
141
else
37)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
142
else
143)
else
(if i.val < 222 then
144
else
145))
else
(if i.val < 225 then
(if i.val < 224 then
146
else
147)
else
(if i.val < 226 then
29
else
67)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
68
else
69)
else
(if i.val < 230 then
98
else
148))
else
(if i.val < 233 then
(if i.val < 232 then
149
else
150)
else
(if i.val < 234 then
151
else
(if i.val < 235 then
152
else
38))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
153
else
154)
else
(if i.val < 239 then
155
else
156))
else
(if i.val < 242 then
(if i.val < 241 then
157
else
158)
else
(if i.val < 243 then
159
else
99)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
41
else
160)
else
(if i.val < 247 then
161
else
73))
else
(if i.val < 250 then
(if i.val < 249 then
103
else
162)
else
(if i.val < 251 then
163
else
(if i.val < 252 then
164
else
165)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
166
else
167)
else
(if i.val < 256 then
168
else
169))
else
(if i.val < 259 then
(if i.val < 258 then
170
else
171)
else
(if i.val < 260 then
172
else
173)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
174
else
175)
else
(if i.val < 264 then
176
else
177))
else
(if i.val < 267 then
(if i.val < 266 then
178
else
179)
else
(if i.val < 268 then
93
else
(if i.val < 269 then
180
else
181)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
182
else
96)
else
(if i.val < 273 then
183
else
184))
else
(if i.val < 276 then
(if i.val < 275 then
185
else
186)
else
(if i.val < 277 then
187
else
188)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
97
else
189)
else
(if i.val < 281 then
190
else
191))
else
(if i.val < 284 then
(if i.val < 283 then
102
else
192)
else
(if i.val < 285 then
193
else
194))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
195
else
196)
else
(if i.val < 289 then
34
else
80))
else
(if i.val < 292 then
(if i.val < 291 then
197
else
63)
else
(if i.val < 293 then
198
else
77)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
81
else
8)
else
(if i.val < 297 then
46
else
47))
else
(if i.val < 300 then
(if i.val < 299 then
104
else
105)
else
(if i.val < 301 then
106
else
(if i.val < 302 then
107
else
2))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
62
else
14)
else
(if i.val < 306 then
48
else
63))
else
(if i.val < 309 then
(if i.val < 308 then
64
else
65)
else
(if i.val < 310 then
199
else
200)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
149
else
91)
else
(if i.val < 314 then
201
else
128))
else
(if i.val < 317 then
(if i.val < 316 then
142
else
202)
else
(if i.val < 318 then
203
else
(if i.val < 319 then
140
else
204)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
205
else
66)
else
(if i.val < 323 then
116
else
206))
else
(if i.val < 326 then
(if i.val < 325 then
207
else
208)
else
(if i.val < 327 then
209
else
210)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
144
else
211)
else
(if i.val < 331 then
212
else
111))
else
(if i.val < 334 then
(if i.val < 333 then
119
else
213)
else
(if i.val < 335 then
88
else
(if i.val < 336 then
214
else
215)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
216
else
217)
else
(if i.val < 340 then
70
else
87))
else
(if i.val < 343 then
(if i.val < 342 then
192
else
218)
else
(if i.val < 344 then
129
else
92)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
10
else
12)
else
(if i.val < 348 then
15
else
16))
else
(if i.val < 351 then
(if i.val < 350 then
17
else
108)
else
(if i.val < 352 then
109
else
(if i.val < 353 then
72
else
110)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
112
else
113)
else
(if i.val < 357 then
55
else
114))
else
(if i.val < 360 then
(if i.val < 359 then
115
else
3)
else
(if i.val < 361 then
49
else
50)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
51
else
52)
else
(if i.val < 365 then
53
else
54))
else
(if i.val < 368 then
(if i.val < 367 then
56
else
57)
else
(if i.val < 369 then
58
else
(if i.val < 370 then
59
else
60))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
61
else
117)
else
(if i.val < 374 then
118
else
120))
else
(if i.val < 377 then
(if i.val < 376 then
121
else
122)
else
(if i.val < 378 then
123
else
75)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
124
else
95)
else
(if i.val < 382 then
125
else
126))
else
(if i.val < 385 then
(if i.val < 384 then
127
else
130)
else
(if i.val < 386 then
131
else
(if i.val < 387 then
132
else
133)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
134
else
135)
else
(if i.val < 391 then
136
else
83))
else
(if i.val < 394 then
(if i.val < 393 then
166
else
219)
else
(if i.val < 395 then
220
else
221)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
99
else
222)
else
(if i.val < 399 then
223
else
224))
else
(if i.val < 402 then
(if i.val < 401 then
225
else
226)
else
(if i.val < 403 then
159
else
(if i.val < 404 then
148
else
227))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
179
else
228)
else
(if i.val < 408 then
229
else
230))
else
(if i.val < 411 then
(if i.val < 410 then
89
else
231)
else
(if i.val < 412 then
193
else
232)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
233
else
234)
else
(if i.val < 416 then
173
else
235))
else
(if i.val < 419 then
(if i.val < 418 then
236
else
237)
else
(if i.val < 420 then
238
else
239))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
240
else
69)
else
(if i.val < 424 then
82
else
241))
else
(if i.val < 427 then
(if i.val < 426 then
137
else
242)
else
(if i.val < 428 then
146
else
243)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
138
else
139)
else
(if i.val < 432 then
79
else
181))
else
(if i.val < 435 then
(if i.val < 434 then
76
else
244)
else
(if i.val < 436 then
245
else
(if i.val < 437 then
246
else
247))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
248
else
249)
else
(if i.val < 441 then
250
else
251))
else
(if i.val < 444 then
(if i.val < 443 then
252
else
253)
else
(if i.val < 445 then
254
else
255)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
150
else
170)
else
(if i.val < 449 then
190
else
256))
else
(if i.val < 452 then
(if i.val < 451 then
257
else
258)
else
(if i.val < 453 then
177
else
(if i.val < 454 then
259
else
67)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
68
else
98)
else
(if i.val < 458 then
145
else
151))
else
(if i.val < 461 then
(if i.val < 460 then
152
else
153)
else
(if i.val < 462 then
154
else
260)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
80
else
261)
else
(if i.val < 466 then
262
else
263))
else
(if i.val < 469 then
(if i.val < 468 then
186
else
161)
else
(if i.val < 470 then
264
else
(if i.val < 471 then
265
else
175)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
266
else
94)
else
(if i.val < 475 then
267
else
197))
else
(if i.val < 478 then
(if i.val < 477 then
164
else
86)
else
(if i.val < 479 then
71
else
268)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
191
else
269)
else
(if i.val < 483 then
270
else
196))
else
(if i.val < 486 then
(if i.val < 485 then
271
else
272)
else
(if i.val < 487 then
273
else
(if i.val < 488 then
274
else
275)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
276
else
277)
else
(if i.val < 492 then
278
else
187))
else
(if i.val < 495 then
(if i.val < 494 then
279
else
198)
else
(if i.val < 496 then
280
else
281)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
282
else
283)
else
(if i.val < 500 then
284
else
285))
else
(if i.val < 503 then
(if i.val < 502 then
286
else
171)
else
(if i.val < 504 then
287
else
(if i.val < 505 then
288
else
289))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
290
else
156)
else
(if i.val < 509 then
141
else
291))
else
(if i.val < 512 then
(if i.val < 511 then
292
else
293)
else
(if i.val < 513 then
294
else
97)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
73
else
78)
else
(if i.val < 517 then
102
else
295))
else
(if i.val < 520 then
(if i.val < 519 then
296
else
297)
else
(if i.val < 521 then
298
else
(if i.val < 522 then
93
else
167)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
174
else
85)
else
(if i.val < 526 then
299
else
300))
else
(if i.val < 529 then
(if i.val < 528 then
301
else
302)
else
(if i.val < 530 then
303
else
304)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
305
else
194)
else
(if i.val < 534 then
306
else
184))
else
(if i.val < 537 then
(if i.val < 536 then
307
else
308)
else
(if i.val < 538 then
27
else
(if i.val < 539 then
104
else
105))))))))))
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
106
else
107)
else
(if i.val < 543 then
199
else
200))
else
(if i.val < 546 then
(if i.val < 545 then
149
else
42)
else
(if i.val < 547 then
201
else
128)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
142
else
202)
else
(if i.val < 551 then
203
else
10))
else
(if i.val < 554 then
(if i.val < 553 then
137
else
138)
else
(if i.val < 555 then
139
else
140))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
141
else
37)
else
(if i.val < 559 then
125
else
143))
else
(if i.val < 562 then
(if i.val < 561 then
144
else
145)
else
(if i.val < 563 then
146
else
147)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
243
else
248)
else
(if i.val < 567 then
290
else
309))
else
(if i.val < 570 then
(if i.val < 569 then
310
else
171)
else
(if i.val < 571 then
152
else
(if i.val < 572 then
311
else
163))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
244
else
251)
else
(if i.val < 576 then
226
else
212))
else
(if i.val < 579 then
(if i.val < 578 then
179
else
232)
else
(if i.val < 580 then
123
else
274)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
312
else
235)
else
(if i.val < 584 then
126
else
210))
else
(if i.val < 587 then
(if i.val < 586 then
313
else
314)
else
(if i.val < 588 then
227
else
(if i.val < 589 then
166
else
304)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
135
else
300)
else
(if i.val < 593 then
216
else
272))
else
(if i.val < 596 then
(if i.val < 595 then
254
else
109)
else
(if i.val < 597 then
271
else
315)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
316
else
220)
else
(if i.val < 601 then
222
else
160))
else
(if i.val < 604 then
(if i.val < 603 then
198
else
306)
else
(if i.val < 605 then
317
else
(if i.val < 606 then
221
else
127)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
184
else
214)
else
(if i.val < 610 then
266
else
240))
else
(if i.val < 613 then
(if i.val < 612 then
318
else
219)
else
(if i.val < 614 then
188
else
17)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
156
else
178)
else
(if i.val < 618 then
32
else
285))
else
(if i.val < 621 then
(if i.val < 620 then
246
else
319)
else
(if i.val < 622 then
33
else
(if i.val < 623 then
34
else
35)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
36
else
38)
else
(if i.val < 627 then
39
else
40))
else
(if i.val < 630 then
(if i.val < 629 then
43
else
44)
else
(if i.val < 631 then
204
else
205)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
116
else
206)
else
(if i.val < 635 then
207
else
208))
else
(if i.val < 638 then
(if i.val < 637 then
209
else
211)
else
(if i.val < 639 then
111
else
(if i.val < 640 then
119
else
213))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
215
else
217)
else
(if i.val < 644 then
192
else
218))
else
(if i.val < 647 then
(if i.val < 646 then
129
else
15)
else
(if i.val < 648 then
16
else
108)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
110
else
112)
else
(if i.val < 652 then
113
else
114))
else
(if i.val < 655 then
(if i.val < 654 then
115
else
117)
else
(if i.val < 656 then
118
else
(if i.val < 657 then
120
else
121)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
122
else
124)
else
(if i.val < 661 then
130
else
131))
else
(if i.val < 664 then
(if i.val < 663 then
132
else
133)
else
(if i.val < 665 then
134
else
136)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
223
else
224)
else
(if i.val < 669 then
225
else
159))
else
(if i.val < 672 then
(if i.val < 671 then
148
else
228)
else
(if i.val < 673 then
229
else
(if i.val < 674 then
230
else
231))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
193
else
233)
else
(if i.val < 678 then
234
else
173))
else
(if i.val < 681 then
(if i.val < 680 then
236
else
237)
else
(if i.val < 682 then
238
else
239)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
241
else
242)
else
(if i.val < 686 then
278
else
305))
else
(if i.val < 689 then
(if i.val < 688 then
261
else
320)
else
(if i.val < 690 then
307
else
321))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
322
else
323)
else
(if i.val < 694 then
324
else
175))
else
(if i.val < 697 then
(if i.val < 696 then
282
else
284)
else
(if i.val < 698 then
289
else
280)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
250
else
181)
else
(if i.val < 702 then
293
else
325))
else
(if i.val < 705 then
(if i.val < 704 then
326
else
183)
else
(if i.val < 706 then
165
else
(if i.val < 707 then
150
else
154))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
169
else
299)
else
(if i.val < 711 then
327
else
328))
else
(if i.val < 714 then
(if i.val < 713 then
262
else
162)
else
(if i.val < 715 then
258
else
189)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
158
else
294)
else
(if i.val < 719 then
303
else
281))
else
(if i.val < 722 then
(if i.val < 721 then
302
else
197)
else
(if i.val < 723 then
269
else
(if i.val < 724 then
270
else
296)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
329
else
330)
else
(if i.val < 728 then
331
else
332))
else
(if i.val < 731 then
(if i.val < 730 then
245
else
247)
else
(if i.val < 732 then
298
else
180)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
333
else
256)
else
(if i.val < 736 then
267
else
283))
else
(if i.val < 739 then
(if i.val < 738 then
334
else
286)
else
(if i.val < 740 then
264
else
(if i.val < 741 then
190
else
273)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
257
else
182)
else
(if i.val < 745 then
259
else
167))
else
(if i.val < 748 then
(if i.val < 747 then
249
else
151)
else
(if i.val < 749 then
153
else
260)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
170
else
263)
else
(if i.val < 753 then
186
else
161))
else
(if i.val < 756 then
(if i.val < 755 then
265
else
168)
else
(if i.val < 757 then
176
else
(if i.val < 758 then
174
else
196)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
335
else
172)
else
(if i.val < 762 then
157
else
336))
else
(if i.val < 765 then
(if i.val < 764 then
277
else
337)
else
(if i.val < 766 then
338
else
252)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
339
else
288)
else
(if i.val < 770 then
268
else
276))
else
(if i.val < 773 then
(if i.val < 772 then
301
else
340)
else
(if i.val < 774 then
279
else
(if i.val < 775 then
341
else
185))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
187
else
275)
else
(if i.val < 779 then
342
else
292))
else
(if i.val < 782 then
(if i.val < 781 then
194
else
253)
else
(if i.val < 783 then
308
else
297)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
343
else
191)
else
(if i.val < 787 then
344
else
345))
else
(if i.val < 790 then
(if i.val < 789 then
346
else
287)
else
(if i.val < 791 then
347
else
(if i.val < 792 then
195
else
348)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
349
else
164)
else
(if i.val < 796 then
64
else
65))
else
(if i.val < 799 then
(if i.val < 798 then
199
else
200)
else
(if i.val < 800 then
42
else
91)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
201
else
202)
else
(if i.val < 804 then
203
else
82))
else
(if i.val < 807 then
(if i.val < 806 then
243
else
248)
else
(if i.val < 808 then
92
else
(if i.val < 809 then
290
else
309)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
310
else
311)
else
(if i.val < 813 then
244
else
251))
else
(if i.val < 816 then
(if i.val < 815 then
226
else
212)
else
(if i.val < 817 then
232
else
274)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
312
else
235)
else
(if i.val < 821 then
32
else
33))
else
(if i.val < 824 then
(if i.val < 823 then
79
else
76)
else
(if i.val < 825 then
245
else
88))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
246
else
247)
else
(if i.val < 829 then
249
else
250))
else
(if i.val < 832 then
(if i.val < 831 then
252
else
253)
else
(if i.val < 833 then
254
else
255)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
256
else
225)
else
(if i.val < 837 then
257
else
210))
else
(if i.val < 840 then
(if i.val < 839 then
258
else
259)
else
(if i.val < 841 then
218
else
(if i.val < 842 then
279
else
315))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
263
else
36)
else
(if i.val < 846 then
295
else
330))
else
(if i.val < 849 then
(if i.val < 848 then
286
else
242)
else
(if i.val < 850 then
275
else
334)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
213
else
229)
else
(if i.val < 854 then
100
else
306))
else
(if i.val < 857 then
(if i.val < 856 then
296
else
283)
else
(if i.val < 858 then
224
else
(if i.val < 859 then
305
else
300)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
323
else
207)
else
(if i.val < 863 then
350
else
351))
else
(if i.val < 866 then
(if i.val < 865 then
219
else
291)
else
(if i.val < 867 then
231
else
222)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
87
else
342)
else
(if i.val < 871 then
293
else
289))
else
(if i.val < 874 then
(if i.val < 873 then
84
else
204)
else
(if i.val < 875 then
71
else
(if i.val < 876 then
343
else
308)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
322
else
268)
else
(if i.val < 880 then
265
else
39))
else
(if i.val < 883 then
(if i.val < 882 then
44
else
94)
else
(if i.val < 884 then
316
else
318)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
320
else
208)
else
(if i.val < 888 then
234
else
236))
else
(if i.val < 891 then
(if i.val < 890 then
271
else
262)
else
(if i.val < 892 then
228
else
(if i.val < 893 then
241
else
297)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
302
else
278)
else
(if i.val < 897 then
324
else
285))
else
(if i.val < 900 then
(if i.val < 899 then
344
else
240)
else
(if i.val < 901 then
314
else
337)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
346
else
74)
else
(if i.val < 905 then
78
else
85))
else
(if i.val < 908 then
(if i.val < 907 then
86
else
89)
else
(if i.val < 909 then
90
else
(if i.val < 910 then
101
else
313))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
227
else
304)
else
(if i.val < 914 then
216
else
272))
else
(if i.val < 917 then
(if i.val < 916 then
220
else
317)
else
(if i.val < 918 then
221
else
214)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
266
else
319)
else
(if i.val < 922 then
40
else
43))
else
(if i.val < 925 then
(if i.val < 924 then
205
else
206)
else
(if i.val < 926 then
209
else
(if i.val < 927 then
211
else
215)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
217
else
223)
else
(if i.val < 931 then
230
else
233))
else
(if i.val < 934 then
(if i.val < 933 then
237
else
238)
else
(if i.val < 935 then
239
else
261)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
307
else
321)
else
(if i.val < 939 then
282
else
284))
else
(if i.val < 942 then
(if i.val < 941 then
280
else
325)
else
(if i.val < 943 then
326
else
(if i.val < 944 then
299
else
327))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
328
else
294)
else
(if i.val < 948 then
303
else
281))
else
(if i.val < 951 then
(if i.val < 950 then
269
else
270)
else
(if i.val < 952 then
329
else
331)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
332
else
276)
else
(if i.val < 956 then
298
else
352))
else
(if i.val < 959 then
(if i.val < 958 then
353
else
338)
else
(if i.val < 960 then
273
else
335))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
292
else
345)
else
(if i.val < 964 then
336
else
354))
else
(if i.val < 967 then
(if i.val < 966 then
277
else
355)
else
(if i.val < 968 then
356
else
264)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
333
else
267)
else
(if i.val < 972 then
340
else
260))
else
(if i.val < 975 then
(if i.val < 974 then
341
else
287)
else
(if i.val < 976 then
339
else
(if i.val < 977 then
288
else
357))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
301
else
348)
else
(if i.val < 981 then
358
else
349))
else
(if i.val < 984 then
(if i.val < 983 then
359
else
347)
else
(if i.val < 985 then
143
else
147)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
309
else
310)
else
(if i.val < 989 then
311
else
163))
else
(if i.val < 992 then
(if i.val < 991 then
312
else
195)
else
(if i.val < 993 then
189
else
(if i.val < 994 then
185
else
315)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
162
else
330)
else
(if i.val < 998 then
165
else
334))
else
(if i.val < 1001 then
(if i.val < 1000 then
169
else
100)
else
(if i.val < 1002 then
155
else
74)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
77
else
319)
else
(if i.val < 1006 then
103
else
180))
else
(if i.val < 1009 then
(if i.val < 1008 then
333
else
90)
else
(if i.val < 1010 then
317
else
(if i.val < 1011 then
101
else
324)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
182
else
329)
else
(if i.val < 1015 then
327
else
321))
else
(if i.val < 1018 then
(if i.val < 1017 then
84
else
342)
else
(if i.val < 1019 then
313
else
336)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
326
else
157)
else
(if i.val < 1023 then
332
else
343))
else
(if i.val < 1026 then
(if i.val < 1025 then
340
else
344)
else
(if i.val < 1027 then
353
else
(if i.val < 1028 then
316
else
178)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
328
else
176)
else
(if i.val < 1032 then
323
else
188))
else
(if i.val < 1035 then
(if i.val < 1034 then
351
else
352)
else
(if i.val < 1036 then
335
else
158)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
345
else
350)
else
(if i.val < 1040 then
322
else
314))
else
(if i.val < 1043 then
(if i.val < 1042 then
318
else
339)
else
(if i.val < 1044 then
325
else
(if i.val < 1045 then
331
else
355))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
172
else
356)
else
(if i.val < 1049 then
357
else
96))
else
(if i.val < 1052 then
(if i.val < 1051 then
160
else
168)
else
(if i.val < 1053 then
183
else
81)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
320
else
337)
else
(if i.val < 1057 then
346
else
338))
else
(if i.val < 1060 then
(if i.val < 1059 then
354
else
341)
else
(if i.val < 1061 then
347
else
(if i.val < 1062 then
358
else
348)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
349
else
359)
else
(if i.val < 1066 then
255
else
177))
else
(if i.val < 1069 then
(if i.val < 1068 then
295
else
155)
else
(if i.val < 1070 then
353
else
351)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
352
else
291)
else
(if i.val < 1074 then
359
else
350))
else
(if i.val < 1077 then
(if i.val < 1076 then
357
else
358)
else
(if i.val < 1078 then
354
else
(if i.val < 1079 then
355
else
356)))))))))))

def g32p_row06_cosetDistances1 : Fin 1080 → ℕ :=
  fun i => (if i.val < 540 then
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
2
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
2
else
1)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
2
else
2)
else
(if i.val < 27 then
0
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
2
else
0)
else
(if i.val < 31 then
0
else
(if i.val < 32 then
0
else
0))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
0
else
0)
else
(if i.val < 36 then
2
else
0))
else
(if i.val < 39 then
(if i.val < 38 then
0
else
2)
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
0)
else
(if i.val < 44 then
0
else
0))
else
(if i.val < 47 then
(if i.val < 46 then
0
else
0)
else
(if i.val < 48 then
0
else
(if i.val < 49 then
0
else
0)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
0
else
0)
else
(if i.val < 53 then
0
else
0))
else
(if i.val < 56 then
(if i.val < 55 then
0
else
2)
else
(if i.val < 57 then
1
else
0)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
0
else
0)
else
(if i.val < 61 then
1
else
2))
else
(if i.val < 64 then
(if i.val < 63 then
0
else
0)
else
(if i.val < 65 then
0
else
(if i.val < 66 then
2
else
2)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
2
else
1)
else
(if i.val < 70 then
1
else
1))
else
(if i.val < 73 then
(if i.val < 72 then
2
else
2)
else
(if i.val < 74 then
1
else
2)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
2
else
2)
else
(if i.val < 78 then
0
else
0))
else
(if i.val < 81 then
(if i.val < 80 then
0
else
0)
else
(if i.val < 82 then
0
else
(if i.val < 83 then
0
else
0)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
0
else
0)
else
(if i.val < 87 then
0
else
2))
else
(if i.val < 90 then
(if i.val < 89 then
2
else
0)
else
(if i.val < 91 then
1
else
2)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
0
else
0)
else
(if i.val < 95 then
0
else
1))
else
(if i.val < 98 then
(if i.val < 97 then
2
else
2)
else
(if i.val < 99 then
0
else
(if i.val < 100 then
0
else
0))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
0
else
0)
else
(if i.val < 104 then
0
else
0))
else
(if i.val < 107 then
(if i.val < 106 then
0
else
0)
else
(if i.val < 108 then
0
else
0)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
0
else
0)
else
(if i.val < 112 then
0
else
0))
else
(if i.val < 115 then
(if i.val < 114 then
0
else
1)
else
(if i.val < 116 then
0
else
(if i.val < 117 then
0
else
0)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
0
else
0)
else
(if i.val < 121 then
0
else
0))
else
(if i.val < 124 then
(if i.val < 123 then
0
else
0)
else
(if i.val < 125 then
0
else
0)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
0
else
2)
else
(if i.val < 129 then
0
else
0))
else
(if i.val < 132 then
(if i.val < 131 then
0
else
0)
else
(if i.val < 133 then
0
else
(if i.val < 134 then
0
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
0
else
0)
else
(if i.val < 138 then
0
else
1))
else
(if i.val < 141 then
(if i.val < 140 then
2
else
2)
else
(if i.val < 142 then
1
else
1)))
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
0)
else
(if i.val < 150 then
0
else
0))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
0
else
2)
else
(if i.val < 154 then
0
else
0))
else
(if i.val < 157 then
(if i.val < 156 then
0
else
0)
else
(if i.val < 158 then
2
else
0)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
0
else
1)
else
(if i.val < 162 then
2
else
2))
else
(if i.val < 165 then
(if i.val < 164 then
2
else
2)
else
(if i.val < 166 then
2
else
(if i.val < 167 then
2
else
2))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
1
else
1)
else
(if i.val < 171 then
1
else
1))
else
(if i.val < 174 then
(if i.val < 173 then
1
else
1)
else
(if i.val < 175 then
1
else
2)))
else
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
(if i.val < 184 then
2
else
2)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
0
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
0
else
0)
else
(if i.val < 192 then
0
else
0)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
0
else
2)
else
(if i.val < 196 then
0
else
2))
else
(if i.val < 199 then
(if i.val < 198 then
0
else
0)
else
(if i.val < 200 then
0
else
(if i.val < 201 then
0
else
0)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
0
else
0)
else
(if i.val < 205 then
0
else
1))
else
(if i.val < 208 then
(if i.val < 207 then
0
else
0)
else
(if i.val < 209 then
0
else
0)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
2
else
2)
else
(if i.val < 213 then
2
else
0))
else
(if i.val < 216 then
(if i.val < 215 then
0
else
0)
else
(if i.val < 217 then
0
else
(if i.val < 218 then
0
else
1)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
0
else
0)
else
(if i.val < 222 then
0
else
0))
else
(if i.val < 225 then
(if i.val < 224 then
0
else
0)
else
(if i.val < 226 then
1
else
2)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
2
else
2)
else
(if i.val < 230 then
2
else
0))
else
(if i.val < 233 then
(if i.val < 232 then
0
else
0)
else
(if i.val < 234 then
0
else
(if i.val < 235 then
0
else
1))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
0))
else
(if i.val < 242 then
(if i.val < 241 then
0
else
0)
else
(if i.val < 243 then
0
else
2)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
1
else
0)
else
(if i.val < 247 then
0
else
2))
else
(if i.val < 250 then
(if i.val < 249 then
2
else
0)
else
(if i.val < 251 then
0
else
(if i.val < 252 then
0
else
0)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
0
else
0)
else
(if i.val < 256 then
0
else
0))
else
(if i.val < 259 then
(if i.val < 258 then
0
else
0)
else
(if i.val < 260 then
0
else
0)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
0
else
0)
else
(if i.val < 264 then
0
else
0))
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
0
else
0)))))))))
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
2)
else
(if i.val < 273 then
0
else
0))
else
(if i.val < 276 then
(if i.val < 275 then
0
else
0)
else
(if i.val < 277 then
0
else
0)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
2
else
0)
else
(if i.val < 281 then
0
else
0))
else
(if i.val < 284 then
(if i.val < 283 then
2
else
0)
else
(if i.val < 285 then
0
else
0))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
0
else
0)
else
(if i.val < 289 then
1
else
2))
else
(if i.val < 292 then
(if i.val < 291 then
0
else
2)
else
(if i.val < 293 then
0
else
2)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
2
else
2)
else
(if i.val < 297 then
1
else
1))
else
(if i.val < 300 then
(if i.val < 299 then
2
else
2)
else
(if i.val < 301 then
2
else
(if i.val < 302 then
2
else
1))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
1
else
2)
else
(if i.val < 306 then
1
else
1))
else
(if i.val < 309 then
(if i.val < 308 then
1
else
1)
else
(if i.val < 310 then
0
else
0)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
2
else
1)
else
(if i.val < 314 then
0
else
2))
else
(if i.val < 317 then
(if i.val < 316 then
2
else
0)
else
(if i.val < 318 then
0
else
(if i.val < 319 then
2
else
0)))))
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
2
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
2
else
0)
else
(if i.val < 331 then
0
else
2))
else
(if i.val < 334 then
(if i.val < 333 then
2
else
0)
else
(if i.val < 335 then
1
else
(if i.val < 336 then
0
else
0)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
0
else
0)
else
(if i.val < 340 then
1
else
1))
else
(if i.val < 343 then
(if i.val < 342 then
2
else
0)
else
(if i.val < 344 then
2
else
1)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
2
else
2)
else
(if i.val < 348 then
2
else
2))
else
(if i.val < 351 then
(if i.val < 350 then
2
else
2)
else
(if i.val < 352 then
2
else
(if i.val < 353 then
1
else
2)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
2
else
2)
else
(if i.val < 357 then
1
else
2))
else
(if i.val < 360 then
(if i.val < 359 then
2
else
1)
else
(if i.val < 361 then
1
else
1)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
1
else
1)
else
(if i.val < 365 then
1
else
1))
else
(if i.val < 368 then
(if i.val < 367 then
1
else
1)
else
(if i.val < 369 then
1
else
(if i.val < 370 then
1
else
1))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
1
else
2)
else
(if i.val < 374 then
2
else
2))
else
(if i.val < 377 then
(if i.val < 376 then
2
else
2)
else
(if i.val < 378 then
2
else
1)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
2
else
1)
else
(if i.val < 382 then
2
else
2))
else
(if i.val < 385 then
(if i.val < 384 then
2
else
2)
else
(if i.val < 386 then
2
else
(if i.val < 387 then
2
else
2)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
2
else
2)
else
(if i.val < 391 then
2
else
1))
else
(if i.val < 394 then
(if i.val < 393 then
2
else
0)
else
(if i.val < 395 then
0
else
0)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
1
else
0)
else
(if i.val < 399 then
0
else
0))
else
(if i.val < 402 then
(if i.val < 401 then
0
else
0)
else
(if i.val < 403 then
2
else
(if i.val < 404 then
2
else
0))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
2
else
0)
else
(if i.val < 408 then
0
else
0))
else
(if i.val < 411 then
(if i.val < 410 then
1
else
0)
else
(if i.val < 412 then
2
else
0)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
0
else
0)
else
(if i.val < 416 then
2
else
0))
else
(if i.val < 419 then
(if i.val < 418 then
0
else
0)
else
(if i.val < 420 then
0
else
0))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
0
else
1)
else
(if i.val < 424 then
1
else
0))
else
(if i.val < 427 then
(if i.val < 426 then
2
else
0)
else
(if i.val < 428 then
2
else
0)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
2
else
2)
else
(if i.val < 432 then
1
else
2))
else
(if i.val < 435 then
(if i.val < 434 then
1
else
0)
else
(if i.val < 436 then
0
else
(if i.val < 437 then
0
else
0))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
0
else
0)
else
(if i.val < 441 then
0
else
0))
else
(if i.val < 444 then
(if i.val < 443 then
0
else
0)
else
(if i.val < 445 then
0
else
0)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
2
else
2)
else
(if i.val < 449 then
2
else
0))
else
(if i.val < 452 then
(if i.val < 451 then
0
else
0)
else
(if i.val < 453 then
2
else
(if i.val < 454 then
0
else
1)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
1
else
1)
else
(if i.val < 458 then
2
else
2))
else
(if i.val < 461 then
(if i.val < 460 then
2
else
2)
else
(if i.val < 462 then
2
else
0)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
1
else
0)
else
(if i.val < 466 then
0
else
0))
else
(if i.val < 469 then
(if i.val < 468 then
2
else
2)
else
(if i.val < 470 then
0
else
(if i.val < 471 then
0
else
2)))))))
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
2))
else
(if i.val < 478 then
(if i.val < 477 then
2
else
1)
else
(if i.val < 479 then
1
else
0)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
2
else
0)
else
(if i.val < 483 then
0
else
2))
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
(if i.val < 488 then
0
else
0)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
0
else
0)
else
(if i.val < 492 then
0
else
2))
else
(if i.val < 495 then
(if i.val < 494 then
0
else
2)
else
(if i.val < 496 then
0
else
0)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
0
else
0)
else
(if i.val < 500 then
0
else
0))
else
(if i.val < 503 then
(if i.val < 502 then
0
else
2)
else
(if i.val < 504 then
0
else
(if i.val < 505 then
0
else
0))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
0
else
2)
else
(if i.val < 509 then
2
else
0))
else
(if i.val < 512 then
(if i.val < 511 then
0
else
0)
else
(if i.val < 513 then
0
else
1)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
1
else
1)
else
(if i.val < 517 then
1
else
0))
else
(if i.val < 520 then
(if i.val < 519 then
0
else
0)
else
(if i.val < 521 then
0
else
(if i.val < 522 then
1
else
2)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
2
else
1)
else
(if i.val < 526 then
0
else
0))
else
(if i.val < 529 then
(if i.val < 528 then
0
else
0)
else
(if i.val < 530 then
0
else
0)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
0
else
2)
else
(if i.val < 534 then
0
else
2))
else
(if i.val < 537 then
(if i.val < 536 then
0
else
0)
else
(if i.val < 538 then
2
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
1
else
1)
else
(if i.val < 543 then
2
else
2))
else
(if i.val < 546 then
(if i.val < 545 then
1
else
2)
else
(if i.val < 547 then
2
else
1)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
1
else
2)
else
(if i.val < 551 then
2
else
1))
else
(if i.val < 554 then
(if i.val < 553 then
1
else
1)
else
(if i.val < 555 then
1
else
1))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
1
else
2)
else
(if i.val < 559 then
1
else
1))
else
(if i.val < 562 then
(if i.val < 561 then
1
else
1)
else
(if i.val < 563 then
1
else
1)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
2
else
2)
else
(if i.val < 567 then
2
else
0))
else
(if i.val < 570 then
(if i.val < 569 then
0
else
1)
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
2
else
2)
else
(if i.val < 576 then
2
else
2))
else
(if i.val < 579 then
(if i.val < 578 then
1
else
2)
else
(if i.val < 580 then
1
else
2)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
0
else
2)
else
(if i.val < 584 then
1
else
2))
else
(if i.val < 587 then
(if i.val < 586 then
0
else
0)
else
(if i.val < 588 then
2
else
(if i.val < 589 then
1
else
2)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
1
else
2)
else
(if i.val < 593 then
2
else
2))
else
(if i.val < 596 then
(if i.val < 595 then
2
else
1)
else
(if i.val < 597 then
2
else
0)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
0
else
2)
else
(if i.val < 601 then
2
else
1))
else
(if i.val < 604 then
(if i.val < 603 then
1
else
2)
else
(if i.val < 605 then
0
else
(if i.val < 606 then
2
else
1)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
1
else
2)
else
(if i.val < 610 then
2
else
2))
else
(if i.val < 613 then
(if i.val < 612 then
0
else
2)
else
(if i.val < 614 then
1
else
1)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
1
else
1)
else
(if i.val < 618 then
2
else
2))
else
(if i.val < 621 then
(if i.val < 620 then
2
else
0)
else
(if i.val < 622 then
2
else
(if i.val < 623 then
2
else
2)))))
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
1
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
1
else
(if i.val < 640 then
1
else
2))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
2
else
2)
else
(if i.val < 644 then
1
else
2))
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
1)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
1
else
1)
else
(if i.val < 652 then
1
else
1))
else
(if i.val < 655 then
(if i.val < 654 then
1
else
1)
else
(if i.val < 656 then
1
else
(if i.val < 657 then
1
else
1)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
1
else
1)
else
(if i.val < 661 then
1
else
1))
else
(if i.val < 664 then
(if i.val < 663 then
1
else
1)
else
(if i.val < 665 then
1
else
1)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
2
else
2)
else
(if i.val < 669 then
2
else
1))
else
(if i.val < 672 then
(if i.val < 671 then
1
else
2)
else
(if i.val < 673 then
2
else
(if i.val < 674 then
2
else
2))))))))
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
2)
else
(if i.val < 678 then
2
else
1))
else
(if i.val < 681 then
(if i.val < 680 then
2
else
2)
else
(if i.val < 682 then
2
else
2)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
2
else
2)
else
(if i.val < 686 then
2
else
2))
else
(if i.val < 689 then
(if i.val < 688 then
2
else
0)
else
(if i.val < 690 then
2
else
0))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
0
else
0)
else
(if i.val < 694 then
0
else
1))
else
(if i.val < 697 then
(if i.val < 696 then
2
else
2)
else
(if i.val < 698 then
2
else
2)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
2
else
1)
else
(if i.val < 702 then
2
else
0))
else
(if i.val < 705 then
(if i.val < 704 then
0
else
1)
else
(if i.val < 706 then
1
else
(if i.val < 707 then
1
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
2)
else
(if i.val < 711 then
0
else
0))
else
(if i.val < 714 then
(if i.val < 713 then
2
else
1)
else
(if i.val < 715 then
2
else
1)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
1
else
2)
else
(if i.val < 719 then
2
else
2))
else
(if i.val < 722 then
(if i.val < 721 then
2
else
1)
else
(if i.val < 723 then
2
else
(if i.val < 724 then
2
else
2)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
0
else
0)
else
(if i.val < 728 then
0
else
0))
else
(if i.val < 731 then
(if i.val < 730 then
2
else
2)
else
(if i.val < 732 then
2
else
1)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
0
else
2)
else
(if i.val < 736 then
2
else
2))
else
(if i.val < 739 then
(if i.val < 738 then
0
else
2)
else
(if i.val < 740 then
2
else
(if i.val < 741 then
1
else
2)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
2
else
1)
else
(if i.val < 745 then
2
else
1))
else
(if i.val < 748 then
(if i.val < 747 then
2
else
1)
else
(if i.val < 749 then
1
else
2)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
1
else
2)
else
(if i.val < 753 then
1
else
1))
else
(if i.val < 756 then
(if i.val < 755 then
2
else
1)
else
(if i.val < 757 then
1
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
1
else
0))
else
(if i.val < 765 then
(if i.val < 764 then
2
else
0)
else
(if i.val < 766 then
0
else
2)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
0
else
2)
else
(if i.val < 770 then
2
else
2))
else
(if i.val < 773 then
(if i.val < 772 then
2
else
0)
else
(if i.val < 774 then
2
else
(if i.val < 775 then
0
else
1))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1
else
2)
else
(if i.val < 779 then
0
else
2))
else
(if i.val < 782 then
(if i.val < 781 then
1
else
2)
else
(if i.val < 783 then
2
else
2)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
0
else
1)
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
2)
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
0
else
1)
else
(if i.val < 796 then
2
else
2))
else
(if i.val < 799 then
(if i.val < 798 then
1
else
1)
else
(if i.val < 800 then
1
else
2)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
1
else
1)
else
(if i.val < 804 then
1
else
2))
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
1
else
2)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
2
else
2)
else
(if i.val < 813 then
1
else
1))
else
(if i.val < 816 then
(if i.val < 815 then
1
else
1)
else
(if i.val < 817 then
1
else
1)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
2
else
1)
else
(if i.val < 821 then
1
else
1))
else
(if i.val < 824 then
(if i.val < 823 then
2
else
2)
else
(if i.val < 825 then
1
else
2))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
1
else
1)
else
(if i.val < 829 then
1
else
1))
else
(if i.val < 832 then
(if i.val < 831 then
1
else
1)
else
(if i.val < 833 then
1
else
1)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
1
else
1)
else
(if i.val < 837 then
1
else
1))
else
(if i.val < 840 then
(if i.val < 839 then
1
else
1)
else
(if i.val < 841 then
1
else
(if i.val < 842 then
1
else
2))))))
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
1
else
2))
else
(if i.val < 849 then
(if i.val < 848 then
1
else
1)
else
(if i.val < 850 then
1
else
2)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
1
else
1)
else
(if i.val < 854 then
2
else
1))
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
1
else
1)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
2
else
1)
else
(if i.val < 863 then
0
else
0))
else
(if i.val < 866 then
(if i.val < 865 then
1
else
1)
else
(if i.val < 867 then
1
else
1)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
2
else
2)
else
(if i.val < 871 then
1
else
1))
else
(if i.val < 874 then
(if i.val < 873 then
2
else
1)
else
(if i.val < 875 then
2
else
(if i.val < 876 then
2
else
1)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
2
else
1)
else
(if i.val < 880 then
1
else
1))
else
(if i.val < 883 then
(if i.val < 882 then
1
else
2)
else
(if i.val < 884 then
2
else
2)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
2
else
1)
else
(if i.val < 888 then
1
else
1))
else
(if i.val < 891 then
(if i.val < 890 then
1
else
1)
else
(if i.val < 892 then
1
else
(if i.val < 893 then
1
else
1)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
1
else
1)
else
(if i.val < 897 then
2
else
1))
else
(if i.val < 900 then
(if i.val < 899 then
2
else
1)
else
(if i.val < 901 then
2
else
2)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
2
else
2)
else
(if i.val < 905 then
2
else
2))
else
(if i.val < 908 then
(if i.val < 907 then
2
else
2)
else
(if i.val < 909 then
2
else
(if i.val < 910 then
2
else
2))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
1
else
1)
else
(if i.val < 914 then
1
else
1))
else
(if i.val < 917 then
(if i.val < 916 then
1
else
2)
else
(if i.val < 918 then
1
else
1)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
1
else
2)
else
(if i.val < 922 then
1
else
1))
else
(if i.val < 925 then
(if i.val < 924 then
1
else
1)
else
(if i.val < 926 then
1
else
(if i.val < 927 then
1
else
1)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
1
else
1)
else
(if i.val < 931 then
1
else
1))
else
(if i.val < 934 then
(if i.val < 933 then
1
else
1)
else
(if i.val < 935 then
1
else
1)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1
else
2)
else
(if i.val < 939 then
1
else
1))
else
(if i.val < 942 then
(if i.val < 941 then
1
else
2)
else
(if i.val < 943 then
2
else
(if i.val < 944 then
1
else
2))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
2
else
1)
else
(if i.val < 948 then
1
else
1))
else
(if i.val < 951 then
(if i.val < 950 then
1
else
1)
else
(if i.val < 952 then
2
else
2)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
2
else
1)
else
(if i.val < 956 then
1
else
0))
else
(if i.val < 959 then
(if i.val < 958 then
0
else
2)
else
(if i.val < 960 then
1
else
2))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
1
else
2)
else
(if i.val < 964 then
2
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
0
else
1)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
2
else
1)
else
(if i.val < 972 then
2
else
1))
else
(if i.val < 975 then
(if i.val < 974 then
2
else
1)
else
(if i.val < 976 then
2
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
2)
else
(if i.val < 981 then
0
else
2))
else
(if i.val < 984 then
(if i.val < 983 then
0
else
2)
else
(if i.val < 985 then
2
else
2)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
1
else
1)
else
(if i.val < 989 then
1
else
2))
else
(if i.val < 992 then
(if i.val < 991 then
1
else
2)
else
(if i.val < 993 then
2
else
(if i.val < 994 then
2
else
1)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
2
else
1)
else
(if i.val < 998 then
2
else
1))
else
(if i.val < 1001 then
(if i.val < 1000 then
2
else
1)
else
(if i.val < 1002 then
2
else
1)))
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
2))
else
(if i.val < 1009 then
(if i.val < 1008 then
1
else
1)
else
(if i.val < 1010 then
1
else
(if i.val < 1011 then
1
else
1)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
2
else
1)
else
(if i.val < 1015 then
1
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
1
else
1)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
1
else
2)
else
(if i.val < 1023 then
1
else
1))
else
(if i.val < 1026 then
(if i.val < 1025 then
1
else
1)
else
(if i.val < 1027 then
2
else
(if i.val < 1028 then
1
else
2)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
1
else
2)
else
(if i.val < 1032 then
1
else
2))
else
(if i.val < 1035 then
(if i.val < 1034 then
2
else
2)
else
(if i.val < 1036 then
1
else
2)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
1
else
2)
else
(if i.val < 1040 then
1
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
1
else
(if i.val < 1045 then
1
else
2))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
2
else
2)
else
(if i.val < 1049 then
2
else
1))
else
(if i.val < 1052 then
(if i.val < 1051 then
2
else
2)
else
(if i.val < 1053 then
2
else
1)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
1
else
1)
else
(if i.val < 1057 then
1
else
1))
else
(if i.val < 1060 then
(if i.val < 1059 then
2
else
1)
else
(if i.val < 1061 then
1
else
(if i.val < 1062 then
2
else
1)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
1
else
2)
else
(if i.val < 1066 then
2
else
1))
else
(if i.val < 1069 then
(if i.val < 1068 then
2
else
1)
else
(if i.val < 1070 then
1
else
1)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
1
else
2)
else
(if i.val < 1074 then
1
else
1))
else
(if i.val < 1077 then
(if i.val < 1076 then
1
else
1)
else
(if i.val < 1078 then
1
else
(if i.val < 1079 then
1
else
1)))))))))))

def g32p_row06_cosetRoots1 : Fin 360 → Fin 1080 :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
0
else
1)
else
(if i.val < 3 then
2
else
(if i.val < 4 then
3
else
4)))
else
(if i.val < 8 then
(if i.val < 6 then
5
else
(if i.val < 7 then
7
else
8))
else
(if i.val < 9 then
9
else
(if i.val < 10 then
10
else
11))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
12
else
13)
else
(if i.val < 14 then
14
else
(if i.val < 15 then
15
else
16)))
else
(if i.val < 19 then
(if i.val < 17 then
17
else
(if i.val < 18 then
18
else
19))
else
(if i.val < 20 then
20
else
(if i.val < 21 then
21
else
26)))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
27
else
29)
else
(if i.val < 25 then
30
else
(if i.val < 26 then
31
else
32)))
else
(if i.val < 30 then
(if i.val < 28 then
33
else
(if i.val < 29 then
34
else
36))
else
(if i.val < 31 then
37
else
(if i.val < 32 then
39
else
41))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
42
else
(if i.val < 35 then
43
else
44))
else
(if i.val < 37 then
45
else
(if i.val < 38 then
46
else
47)))
else
(if i.val < 42 then
(if i.val < 40 then
48
else
(if i.val < 41 then
49
else
50))
else
(if i.val < 43 then
51
else
(if i.val < 44 then
52
else
53))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
54
else
57)
else
(if i.val < 48 then
58
else
(if i.val < 49 then
59
else
62)))
else
(if i.val < 53 then
(if i.val < 51 then
63
else
(if i.val < 52 then
64
else
77))
else
(if i.val < 54 then
78
else
(if i.val < 55 then
79
else
80))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
81
else
82)
else
(if i.val < 59 then
83
else
(if i.val < 60 then
84
else
85)))
else
(if i.val < 64 then
(if i.val < 62 then
86
else
(if i.val < 63 then
89
else
92))
else
(if i.val < 65 then
93
else
(if i.val < 66 then
94
else
98)))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
99
else
100)
else
(if i.val < 70 then
101
else
(if i.val < 71 then
102
else
103)))
else
(if i.val < 75 then
(if i.val < 73 then
104
else
(if i.val < 74 then
105
else
106))
else
(if i.val < 76 then
107
else
(if i.val < 77 then
108
else
109))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
110
else
(if i.val < 80 then
111
else
112))
else
(if i.val < 82 then
113
else
(if i.val < 83 then
115
else
116)))
else
(if i.val < 87 then
(if i.val < 85 then
117
else
(if i.val < 86 then
118
else
119))
else
(if i.val < 88 then
120
else
(if i.val < 89 then
121
else
122)))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
123
else
124)
else
(if i.val < 93 then
125
else
(if i.val < 94 then
126
else
128)))
else
(if i.val < 98 then
(if i.val < 96 then
129
else
(if i.val < 97 then
130
else
131))
else
(if i.val < 99 then
132
else
(if i.val < 100 then
133
else
134))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
135
else
136)
else
(if i.val < 104 then
137
else
(if i.val < 105 then
144
else
147)))
else
(if i.val < 109 then
(if i.val < 107 then
148
else
(if i.val < 108 then
149
else
150))
else
(if i.val < 110 then
151
else
(if i.val < 111 then
153
else
154)))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
155
else
156)
else
(if i.val < 115 then
158
else
(if i.val < 116 then
159
else
185)))
else
(if i.val < 120 then
(if i.val < 118 then
186
else
(if i.val < 119 then
188
else
189))
else
(if i.val < 121 then
190
else
(if i.val < 122 then
191
else
192))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
193
else
(if i.val < 125 then
195
else
197))
else
(if i.val < 127 then
198
else
(if i.val < 128 then
199
else
200)))
else
(if i.val < 132 then
(if i.val < 130 then
201
else
(if i.val < 131 then
202
else
203))
else
(if i.val < 133 then
204
else
(if i.val < 134 then
206
else
207))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
208
else
209)
else
(if i.val < 138 then
213
else
(if i.val < 139 then
214
else
215)))
else
(if i.val < 143 then
(if i.val < 141 then
216
else
(if i.val < 142 then
217
else
219))
else
(if i.val < 144 then
220
else
(if i.val < 145 then
221
else
222))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
223
else
224)
else
(if i.val < 149 then
230
else
(if i.val < 150 then
231
else
232)))
else
(if i.val < 154 then
(if i.val < 152 then
233
else
(if i.val < 153 then
234
else
236))
else
(if i.val < 155 then
237
else
(if i.val < 156 then
238
else
239)))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
240
else
241)
else
(if i.val < 160 then
242
else
(if i.val < 161 then
245
else
246)))
else
(if i.val < 165 then
(if i.val < 163 then
249
else
(if i.val < 164 then
250
else
251))
else
(if i.val < 166 then
252
else
(if i.val < 167 then
253
else
254))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
255
else
(if i.val < 170 then
256
else
257))
else
(if i.val < 172 then
258
else
(if i.val < 173 then
259
else
260)))
else
(if i.val < 177 then
(if i.val < 175 then
261
else
(if i.val < 176 then
262
else
263))
else
(if i.val < 178 then
264
else
(if i.val < 179 then
265
else
266))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
268
else
269)
else
(if i.val < 183 then
270
else
(if i.val < 184 then
272
else
273)))
else
(if i.val < 188 then
(if i.val < 186 then
274
else
(if i.val < 187 then
275
else
276))
else
(if i.val < 189 then
277
else
(if i.val < 190 then
279
else
280))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
281
else
283)
else
(if i.val < 194 then
284
else
(if i.val < 195 then
285
else
286)))
else
(if i.val < 199 then
(if i.val < 197 then
287
else
(if i.val < 198 then
290
else
292))
else
(if i.val < 200 then
309
else
(if i.val < 201 then
310
else
313)))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
316
else
317)
else
(if i.val < 205 then
319
else
(if i.val < 206 then
320
else
323)))
else
(if i.val < 210 then
(if i.val < 208 then
324
else
(if i.val < 209 then
325
else
326))
else
(if i.val < 211 then
327
else
(if i.val < 212 then
329
else
330))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
333
else
(if i.val < 215 then
335
else
336))
else
(if i.val < 217 then
337
else
(if i.val < 218 then
338
else
342)))
else
(if i.val < 222 then
(if i.val < 220 then
393
else
(if i.val < 221 then
394
else
395))
else
(if i.val < 223 then
397
else
(if i.val < 224 then
398
else
399))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
400
else
401)
else
(if i.val < 228 then
404
else
(if i.val < 229 then
406
else
407)))
else
(if i.val < 233 then
(if i.val < 231 then
408
else
(if i.val < 232 then
410
else
412))
else
(if i.val < 234 then
413
else
(if i.val < 235 then
414
else
416))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
417
else
418)
else
(if i.val < 239 then
419
else
(if i.val < 240 then
420
else
421)))
else
(if i.val < 244 then
(if i.val < 242 then
424
else
(if i.val < 243 then
426
else
428))
else
(if i.val < 245 then
434
else
(if i.val < 246 then
435
else
436)))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
437
else
438)
else
(if i.val < 250 then
439
else
(if i.val < 251 then
440
else
441)))
else
(if i.val < 255 then
(if i.val < 253 then
442
else
(if i.val < 254 then
443
else
444))
else
(if i.val < 256 then
445
else
(if i.val < 257 then
449
else
450))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
451
else
(if i.val < 260 then
453
else
462))
else
(if i.val < 262 then
464
else
(if i.val < 263 then
465
else
466)))
else
(if i.val < 267 then
(if i.val < 265 then
469
else
(if i.val < 266 then
470
else
472))
else
(if i.val < 268 then
474
else
(if i.val < 269 then
479
else
481)))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
482
else
484)
else
(if i.val < 273 then
485
else
(if i.val < 274 then
486
else
487)))
else
(if i.val < 278 then
(if i.val < 276 then
488
else
(if i.val < 277 then
489
else
490))
else
(if i.val < 279 then
491
else
(if i.val < 280 then
493
else
495))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
496
else
497)
else
(if i.val < 284 then
498
else
(if i.val < 285 then
499
else
500)))
else
(if i.val < 289 then
(if i.val < 287 then
501
else
(if i.val < 288 then
503
else
504))
else
(if i.val < 290 then
505
else
(if i.val < 291 then
506
else
509)))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
510
else
511)
else
(if i.val < 295 then
512
else
(if i.val < 296 then
517
else
518)))
else
(if i.val < 300 then
(if i.val < 298 then
519
else
(if i.val < 299 then
520
else
525))
else
(if i.val < 301 then
526
else
(if i.val < 302 then
527
else
528))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
529
else
(if i.val < 305 then
530
else
531))
else
(if i.val < 307 then
533
else
(if i.val < 308 then
535
else
536)))
else
(if i.val < 312 then
(if i.val < 310 then
567
else
(if i.val < 311 then
568
else
571))
else
(if i.val < 313 then
581
else
(if i.val < 314 then
585
else
586))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
597
else
598)
else
(if i.val < 318 then
604
else
(if i.val < 319 then
611
else
620)))
else
(if i.val < 323 then
(if i.val < 321 then
688
else
(if i.val < 322 then
690
else
691))
else
(if i.val < 324 then
692
else
(if i.val < 325 then
693
else
702))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
703
else
710)
else
(if i.val < 329 then
711
else
(if i.val < 330 then
725
else
726)))
else
(if i.val < 334 then
(if i.val < 332 then
727
else
(if i.val < 333 then
728
else
733))
else
(if i.val < 335 then
737
else
(if i.val < 336 then
759
else
762)))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
764
else
765)
else
(if i.val < 340 then
767
else
(if i.val < 341 then
772
else
774)))
else
(if i.val < 345 then
(if i.val < 343 then
778
else
(if i.val < 344 then
784
else
786))
else
(if i.val < 346 then
787
else
(if i.val < 347 then
788
else
790))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
792
else
(if i.val < 350 then
793
else
862))
else
(if i.val < 352 then
863
else
(if i.val < 353 then
956
else
957)))
else
(if i.val < 357 then
(if i.val < 355 then
964
else
(if i.val < 356 then
966
else
967))
else
(if i.val < 358 then
977
else
(if i.val < 359 then
980
else
982)))))))))

def g32p_row06_cosetLengths1 : Fin 360 → ℕ :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
3
else
3)
else
(if i.val < 3 then
3
else
(if i.val < 4 then
3
else
3)))
else
(if i.val < 8 then
(if i.val < 6 then
3
else
(if i.val < 7 then
3
else
3))
else
(if i.val < 9 then
3
else
(if i.val < 10 then
3
else
3))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
3
else
3)
else
(if i.val < 14 then
3
else
(if i.val < 15 then
3
else
3)))
else
(if i.val < 19 then
(if i.val < 17 then
3
else
(if i.val < 18 then
3
else
3))
else
(if i.val < 20 then
3
else
(if i.val < 21 then
3
else
3)))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
3
else
3)
else
(if i.val < 25 then
3
else
(if i.val < 26 then
3
else
3)))
else
(if i.val < 30 then
(if i.val < 28 then
3
else
(if i.val < 29 then
3
else
3))
else
(if i.val < 31 then
3
else
(if i.val < 32 then
3
else
3))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
3
else
(if i.val < 35 then
3
else
3))
else
(if i.val < 37 then
3
else
(if i.val < 38 then
3
else
3)))
else
(if i.val < 42 then
(if i.val < 40 then
3
else
(if i.val < 41 then
3
else
3))
else
(if i.val < 43 then
3
else
(if i.val < 44 then
3
else
3))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
3
else
3)
else
(if i.val < 48 then
3
else
(if i.val < 49 then
3
else
3)))
else
(if i.val < 53 then
(if i.val < 51 then
3
else
(if i.val < 52 then
3
else
3))
else
(if i.val < 54 then
3
else
(if i.val < 55 then
3
else
3))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
3
else
3)
else
(if i.val < 59 then
3
else
(if i.val < 60 then
3
else
3)))
else
(if i.val < 64 then
(if i.val < 62 then
3
else
(if i.val < 63 then
3
else
3))
else
(if i.val < 65 then
3
else
(if i.val < 66 then
3
else
3)))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
3
else
3)
else
(if i.val < 70 then
3
else
(if i.val < 71 then
3
else
3)))
else
(if i.val < 75 then
(if i.val < 73 then
3
else
(if i.val < 74 then
3
else
3))
else
(if i.val < 76 then
3
else
(if i.val < 77 then
3
else
3))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
3
else
(if i.val < 80 then
3
else
3))
else
(if i.val < 82 then
3
else
(if i.val < 83 then
3
else
3)))
else
(if i.val < 87 then
(if i.val < 85 then
3
else
(if i.val < 86 then
3
else
3))
else
(if i.val < 88 then
3
else
(if i.val < 89 then
3
else
3)))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
3
else
3)
else
(if i.val < 93 then
3
else
(if i.val < 94 then
3
else
3)))
else
(if i.val < 98 then
(if i.val < 96 then
3
else
(if i.val < 97 then
3
else
3))
else
(if i.val < 99 then
3
else
(if i.val < 100 then
3
else
3))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
3
else
3)
else
(if i.val < 104 then
3
else
(if i.val < 105 then
3
else
3)))
else
(if i.val < 109 then
(if i.val < 107 then
3
else
(if i.val < 108 then
3
else
3))
else
(if i.val < 110 then
3
else
(if i.val < 111 then
3
else
3)))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
3
else
3)
else
(if i.val < 115 then
3
else
(if i.val < 116 then
3
else
3)))
else
(if i.val < 120 then
(if i.val < 118 then
3
else
(if i.val < 119 then
3
else
3))
else
(if i.val < 121 then
3
else
(if i.val < 122 then
3
else
3))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
3
else
(if i.val < 125 then
3
else
3))
else
(if i.val < 127 then
3
else
(if i.val < 128 then
3
else
3)))
else
(if i.val < 132 then
(if i.val < 130 then
3
else
(if i.val < 131 then
3
else
3))
else
(if i.val < 133 then
3
else
(if i.val < 134 then
3
else
3))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
3
else
3)
else
(if i.val < 138 then
3
else
(if i.val < 139 then
3
else
3)))
else
(if i.val < 143 then
(if i.val < 141 then
3
else
(if i.val < 142 then
3
else
3))
else
(if i.val < 144 then
3
else
(if i.val < 145 then
3
else
3))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
3
else
3)
else
(if i.val < 149 then
3
else
(if i.val < 150 then
3
else
3)))
else
(if i.val < 154 then
(if i.val < 152 then
3
else
(if i.val < 153 then
3
else
3))
else
(if i.val < 155 then
3
else
(if i.val < 156 then
3
else
3)))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
3
else
3)
else
(if i.val < 160 then
3
else
(if i.val < 161 then
3
else
3)))
else
(if i.val < 165 then
(if i.val < 163 then
3
else
(if i.val < 164 then
3
else
3))
else
(if i.val < 166 then
3
else
(if i.val < 167 then
3
else
3))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
3
else
(if i.val < 170 then
3
else
3))
else
(if i.val < 172 then
3
else
(if i.val < 173 then
3
else
3)))
else
(if i.val < 177 then
(if i.val < 175 then
3
else
(if i.val < 176 then
3
else
3))
else
(if i.val < 178 then
3
else
(if i.val < 179 then
3
else
3))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
3
else
3)
else
(if i.val < 183 then
3
else
(if i.val < 184 then
3
else
3)))
else
(if i.val < 188 then
(if i.val < 186 then
3
else
(if i.val < 187 then
3
else
3))
else
(if i.val < 189 then
3
else
(if i.val < 190 then
3
else
3))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
3
else
3)
else
(if i.val < 194 then
3
else
(if i.val < 195 then
3
else
3)))
else
(if i.val < 199 then
(if i.val < 197 then
3
else
(if i.val < 198 then
3
else
3))
else
(if i.val < 200 then
3
else
(if i.val < 201 then
3
else
3)))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
3
else
3)
else
(if i.val < 205 then
3
else
(if i.val < 206 then
3
else
3)))
else
(if i.val < 210 then
(if i.val < 208 then
3
else
(if i.val < 209 then
3
else
3))
else
(if i.val < 211 then
3
else
(if i.val < 212 then
3
else
3))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
3
else
(if i.val < 215 then
3
else
3))
else
(if i.val < 217 then
3
else
(if i.val < 218 then
3
else
3)))
else
(if i.val < 222 then
(if i.val < 220 then
3
else
(if i.val < 221 then
3
else
3))
else
(if i.val < 223 then
3
else
(if i.val < 224 then
3
else
3))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
3
else
3)
else
(if i.val < 228 then
3
else
(if i.val < 229 then
3
else
3)))
else
(if i.val < 233 then
(if i.val < 231 then
3
else
(if i.val < 232 then
3
else
3))
else
(if i.val < 234 then
3
else
(if i.val < 235 then
3
else
3))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
3
else
3)
else
(if i.val < 239 then
3
else
(if i.val < 240 then
3
else
3)))
else
(if i.val < 244 then
(if i.val < 242 then
3
else
(if i.val < 243 then
3
else
3))
else
(if i.val < 245 then
3
else
(if i.val < 246 then
3
else
3)))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
3
else
3)
else
(if i.val < 250 then
3
else
(if i.val < 251 then
3
else
3)))
else
(if i.val < 255 then
(if i.val < 253 then
3
else
(if i.val < 254 then
3
else
3))
else
(if i.val < 256 then
3
else
(if i.val < 257 then
3
else
3))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
3
else
(if i.val < 260 then
3
else
3))
else
(if i.val < 262 then
3
else
(if i.val < 263 then
3
else
3)))
else
(if i.val < 267 then
(if i.val < 265 then
3
else
(if i.val < 266 then
3
else
3))
else
(if i.val < 268 then
3
else
(if i.val < 269 then
3
else
3)))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
3
else
3)
else
(if i.val < 273 then
3
else
(if i.val < 274 then
3
else
3)))
else
(if i.val < 278 then
(if i.val < 276 then
3
else
(if i.val < 277 then
3
else
3))
else
(if i.val < 279 then
3
else
(if i.val < 280 then
3
else
3))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
3
else
3)
else
(if i.val < 284 then
3
else
(if i.val < 285 then
3
else
3)))
else
(if i.val < 289 then
(if i.val < 287 then
3
else
(if i.val < 288 then
3
else
3))
else
(if i.val < 290 then
3
else
(if i.val < 291 then
3
else
3)))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
3
else
3)
else
(if i.val < 295 then
3
else
(if i.val < 296 then
3
else
3)))
else
(if i.val < 300 then
(if i.val < 298 then
3
else
(if i.val < 299 then
3
else
3))
else
(if i.val < 301 then
3
else
(if i.val < 302 then
3
else
3))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
3
else
(if i.val < 305 then
3
else
3))
else
(if i.val < 307 then
3
else
(if i.val < 308 then
3
else
3)))
else
(if i.val < 312 then
(if i.val < 310 then
3
else
(if i.val < 311 then
3
else
3))
else
(if i.val < 313 then
3
else
(if i.val < 314 then
3
else
3))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
3
else
3)
else
(if i.val < 318 then
3
else
(if i.val < 319 then
3
else
3)))
else
(if i.val < 323 then
(if i.val < 321 then
3
else
(if i.val < 322 then
3
else
3))
else
(if i.val < 324 then
3
else
(if i.val < 325 then
3
else
3))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
3
else
3)
else
(if i.val < 329 then
3
else
(if i.val < 330 then
3
else
3)))
else
(if i.val < 334 then
(if i.val < 332 then
3
else
(if i.val < 333 then
3
else
3))
else
(if i.val < 335 then
3
else
(if i.val < 336 then
3
else
3)))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
3
else
3)
else
(if i.val < 340 then
3
else
(if i.val < 341 then
3
else
3)))
else
(if i.val < 345 then
(if i.val < 343 then
3
else
(if i.val < 344 then
3
else
3))
else
(if i.val < 346 then
3
else
(if i.val < 347 then
3
else
3))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
3
else
(if i.val < 350 then
3
else
3))
else
(if i.val < 352 then
3
else
(if i.val < 353 then
3
else
3)))
else
(if i.val < 357 then
(if i.val < 355 then
3
else
(if i.val < 356 then
3
else
3))
else
(if i.val < 358 then
3
else
(if i.val < 359 then
3
else
3)))))))))

def g32p_row06_cosetCycleNodes1 : Fin 360 → List ℕ :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
[0, 168, 65]
else
[1, 23, 6])
else
(if i.val < 3 then
[2, 302, 161]
else
(if i.val < 4 then
[3, 359, 162]
else
[4, 40, 163])))
else
(if i.val < 8 then
(if i.val < 6 then
[5, 68, 22]
else
(if i.val < 7 then
[7, 69, 24]
else
[8, 70, 25]))
else
(if i.val < 9 then
[9, 56, 295]
else
(if i.val < 10 then
[10, 95, 35]
else
[11, 551, 345]))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
[12, 73, 28]
else
[13, 60, 346])
else
(if i.val < 14 then
[14, 114, 38]
else
(if i.val < 15 then
[15, 90, 304]
else
[16, 646, 347])))
else
(if i.val < 19 then
(if i.val < 17 then
[17, 647, 348]
else
(if i.val < 18 then
[18, 614, 349]
else
[19, 138, 55]))
else
(if i.val < 20 then
[20, 169, 66]
else
(if i.val < 21 then
[21, 170, 67]
else
[26, 145, 71])))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
[27, 171, 72]
else
[29, 172, 74])
else
(if i.val < 25 then
[30, 173, 75]
else
(if i.val < 26 then
[31, 174, 76]
else
[32, 141, 88])))
else
(if i.val < 30 then
(if i.val < 28 then
[33, 142, 537]
else
(if i.val < 29 then
[34, 143, 61]
else
[36, 225, 96]))
else
(if i.val < 31 then
[37, 146, 97]
else
(if i.val < 32 then
[39, 187, 91]
else
[41, 820, 617]))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
[42, 821, 621]
else
(if i.val < 35 then
[43, 288, 622]
else
[44, 205, 623]))
else
(if i.val < 37 then
[45, 844, 624]
else
(if i.val < 38 then
[46, 218, 557]
else
[47, 235, 625])))
else
(if i.val < 42 then
(if i.val < 40 then
[48, 880, 626]
else
(if i.val < 41 then
[49, 921, 627]
else
[50, 244, 127]))
else
(if i.val < 43 then
[51, 799, 545]
else
(if i.val < 44 then
[52, 922, 628]
else
[53, 881, 629]))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
[54, 160, 87]
else
[57, 296, 139])
else
(if i.val < 48 then
[58, 297, 140]
else
(if i.val < 49 then
[59, 305, 164]
else
[62, 360, 165])))
else
(if i.val < 53 then
(if i.val < 51 then
[63, 361, 166]
else
(if i.val < 52 then
[64, 362, 167]
else
[77, 363, 175]))
else
(if i.val < 54 then
[78, 364, 176]
else
(if i.val < 55 then
[79, 365, 177]
else
[80, 356, 157]))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
[81, 366, 178]
else
[82, 367, 179])
else
(if i.val < 59 then
[83, 368, 180]
else
(if i.val < 60 then
[84, 369, 181]
else
[85, 370, 182])))
else
(if i.val < 64 then
(if i.val < 62 then
[86, 371, 183]
else
(if i.val < 63 then
[89, 303, 211]
else
[92, 306, 291]))
else
(if i.val < 65 then
[93, 307, 795]
else
(if i.val < 66 then
[94, 308, 796]
else
[98, 321, 212])))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
[99, 454, 226]
else
[100, 455, 227])
else
(if i.val < 70 then
[101, 422, 228]
else
(if i.val < 71 then
[102, 339, 184]
else
[103, 478, 874])))
else
(if i.val < 75 then
(if i.val < 73 then
[104, 352, 152]
else
(if i.val < 74 then
[105, 514, 247]
else
[106, 1002, 903]))
else
(if i.val < 76 then
[107, 378, 194]
else
(if i.val < 77 then
[108, 433, 823]
else
[109, 1003, 293]))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
[110, 515, 904]
else
(if i.val < 80 then
[111, 431, 822]
else
[112, 463, 289]))
else
(if i.val < 82 then
[113, 1053, 294]
else
(if i.val < 83 then
[115, 423, 804]
else
[116, 391, 210])))
else
(if i.val < 87 then
(if i.val < 85 then
[117, 1016, 872]
else
(if i.val < 86 then
[118, 524, 905]
else
[119, 477, 906]))
else
(if i.val < 88 then
[120, 340, 868]
else
(if i.val < 89 then
[121, 334, 825]
else
[122, 409, 907])))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
[123, 1008, 908]
else
[124, 312, 800])
else
(if i.val < 93 then
[125, 344, 807]
else
(if i.val < 94 then
[126, 521, 267]
else
[128, 473, 882])))
else
(if i.val < 98 then
(if i.val < 96 then
[129, 380, 196]
else
(if i.val < 97 then
[130, 1049, 271]
else
[131, 513, 278]))
else
(if i.val < 99 then
[132, 456, 229]
else
(if i.val < 100 then
[133, 396, 243]
else
[134, 1000, 853]))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
[135, 1010, 909]
else
[136, 516, 282])
else
(if i.val < 104 then
[137, 1005, 248]
else
(if i.val < 105 then
[144, 538, 298]
else
[147, 539, 299])))
else
(if i.val < 109 then
(if i.val < 107 then
[148, 540, 300]
else
(if i.val < 108 then
[149, 541, 301]
else
[150, 648, 350]))
else
(if i.val < 110 then
[151, 595, 351]
else
(if i.val < 111 then
[153, 649, 353]
else
[154, 638, 331])))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
[155, 650, 354]
else
[156, 651, 355])
else
(if i.val < 115 then
[158, 652, 357]
else
(if i.val < 116 then
[159, 653, 358]
else
[185, 632, 322])))
else
(if i.val < 120 then
(if i.val < 118 then
[186, 654, 372]
else
(if i.val < 119 then
[188, 655, 373]
else
[189, 639, 332]))
else
(if i.val < 121 then
[190, 656, 374]
else
(if i.val < 122 then
[191, 657, 375]
else
[192, 658, 376]))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
[193, 579, 377]
else
(if i.val < 125 then
[195, 659, 379]
else
[197, 558, 381]))
else
(if i.val < 127 then
[198, 583, 382]
else
(if i.val < 128 then
[199, 606, 383]
else
[200, 547, 314])))
else
(if i.val < 132 then
(if i.val < 130 then
[201, 645, 343]
else
(if i.val < 131 then
[202, 660, 384]
else
[203, 661, 385]))
else
(if i.val < 133 then
[204, 662, 386]
else
(if i.val < 134 then
[206, 663, 387]
else
[207, 664, 388]))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
[208, 590, 389]
else
[209, 665, 390])
else
(if i.val < 138 then
[213, 552, 425]
else
(if i.val < 139 then
[214, 553, 429]
else
[215, 554, 430])))
else
(if i.val < 143 then
(if i.val < 141 then
[216, 555, 318]
else
(if i.val < 142 then
[217, 556, 508]
else
[219, 548, 315]))
else
(if i.val < 144 then
[220, 559, 984]
else
(if i.val < 145 then
[221, 560, 328]
else
[222, 561, 457]))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
[223, 562, 427]
else
[224, 563, 985])
else
(if i.val < 149 then
[230, 670, 403]
else
(if i.val < 150 then
[231, 544, 311]
else
[232, 706, 446])))
else
(if i.val < 154 then
(if i.val < 152 then
[233, 747, 458]
else
(if i.val < 153 then
[234, 570, 459]
else
[236, 748, 460]))
else
(if i.val < 155 then
[237, 707, 461]
else
(if i.val < 156 then
[238, 1068, 1001]
else
[239, 615, 507])))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
[240, 761, 1021]
else
[241, 716, 1036])
else
(if i.val < 160 then
[242, 669, 402]
else
(if i.val < 161 then
[245, 601, 1050]
else
[246, 753, 468])))
else
(if i.val < 165 then
(if i.val < 163 then
[249, 713, 995]
else
(if i.val < 164 then
[250, 572, 989]
else
[251, 794, 476]))
else
(if i.val < 166 then
[252, 705, 997]
else
(if i.val < 167 then
[253, 588, 392]
else
[254, 745, 522]))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
[255, 755, 1051]
else
(if i.val < 170 then
[256, 708, 999]
else
[257, 750, 447]))
else
(if i.val < 172 then
[258, 569, 502]
else
(if i.val < 173 then
[259, 760, 1046]
else
[260, 678, 415])))
else
(if i.val < 177 then
(if i.val < 175 then
[261, 757, 523]
else
(if i.val < 176 then
[262, 694, 471]
else
[263, 756, 1030]))
else
(if i.val < 178 then
[264, 1066, 452]
else
(if i.val < 179 then
[265, 616, 1028]
else
[266, 577, 405]))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
[268, 732, 1006]
else
[269, 700, 432])
else
(if i.val < 183 then
[270, 743, 1012]
else
(if i.val < 184 then
[272, 704, 1052]
else
[273, 607, 534])))
else
(if i.val < 188 then
(if i.val < 186 then
[274, 775, 993]
else
(if i.val < 187 then
[275, 752, 467]
else
[276, 776, 492]))
else
(if i.val < 189 then
[277, 613, 1032]
else
(if i.val < 190 then
[279, 715, 992]
else
[280, 740, 448]))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
[281, 785, 480]
else
[283, 643, 341])
else
(if i.val < 194 then
[284, 675, 411]
else
(if i.val < 195 then
[285, 780, 532]
else
[286, 791, 991])))
else
(if i.val < 199 then
(if i.val < 197 then
[287, 758, 483]
else
(if i.val < 198 then
[290, 721, 475]
else
[292, 602, 494]))
else
(if i.val < 200 then
[309, 797, 542]
else
(if i.val < 201 then
[310, 798, 543]
else
[313, 801, 546])))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
[316, 802, 549]
else
[317, 803, 550])
else
(if i.val < 205 then
[319, 873, 630]
else
(if i.val < 206 then
[320, 923, 631]
else
[323, 924, 633])))
else
(if i.val < 210 then
(if i.val < 208 then
[324, 861, 634]
else
(if i.val < 209 then
[325, 886, 635]
else
[326, 925, 636]))
else
(if i.val < 211 then
[327, 837, 584]
else
(if i.val < 212 then
[329, 926, 637]
else
[330, 815, 576]))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
[333, 851, 640]
else
(if i.val < 215 then
[335, 918, 608]
else
[336, 927, 641]))
else
(if i.val < 217 then
[337, 913, 592]
else
(if i.val < 218 then
[338, 928, 642]
else
[342, 840, 644])))
else
(if i.val < 222 then
(if i.val < 220 then
[393, 864, 612]
else
(if i.val < 221 then
[394, 915, 599]
else
[395, 917, 605]))
else
(if i.val < 223 then
[397, 867, 600]
else
(if i.val < 224 then
[398, 929, 666]
else
[399, 857, 667]))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
[400, 835, 668]
else
[401, 814, 575])
else
(if i.val < 228 then
[404, 911, 587]
else
(if i.val < 229 then
[406, 891, 671]
else
[407, 852, 672])))
else
(if i.val < 233 then
(if i.val < 231 then
[408, 930, 673]
else
(if i.val < 232 then
[410, 866, 674]
else
[412, 816, 578]))
else
(if i.val < 234 then
[413, 931, 676]
else
(if i.val < 235 then
[414, 887, 677]
else
[416, 819, 582]))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
[417, 888, 679]
else
[418, 932, 680])
else
(if i.val < 239 then
[419, 933, 681]
else
(if i.val < 240 then
[420, 934, 682]
else
[421, 899, 610])))
else
(if i.val < 244 then
(if i.val < 242 then
[424, 892, 683]
else
(if i.val < 243 then
[426, 848, 684]
else
[428, 805, 564]))
else
(if i.val < 245 then
[434, 812, 573]
else
(if i.val < 246 then
[435, 824, 729]
else
[436, 826, 619])))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
[437, 827, 730]
else
[438, 806, 565])
else
(if i.val < 250 then
[439, 828, 746]
else
(if i.val < 251 then
[440, 829, 699]
else
[441, 813, 574])))
else
(if i.val < 255 then
(if i.val < 253 then
[442, 830, 766]
else
(if i.val < 254 then
[443, 831, 781]
else
[444, 832, 594]))
else
(if i.val < 256 then
[445, 833, 1065]
else
(if i.val < 257 then
[449, 834, 734]
else
[450, 836, 742]))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
[451, 838, 714]
else
(if i.val < 260 then
[453, 839, 744]
else
[462, 972, 749]))
else
(if i.val < 262 then
[464, 935, 687]
else
(if i.val < 263 then
[465, 890, 712]
else
[466, 843, 751])))
else
(if i.val < 267 then
(if i.val < 265 then
[469, 968, 739]
else
(if i.val < 266 then
[470, 879, 754]
else
[472, 919, 609]))
else
(if i.val < 268 then
[474, 970, 735]
else
(if i.val < 269 then
[479, 878, 769]
else
[481, 949, 722])))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
[482, 950, 723]
else
[484, 889, 596])
else
(if i.val < 273 then
[485, 914, 593]
else
(if i.val < 274 then
[486, 959, 741]
else
[487, 817, 580])))
else
(if i.val < 278 then
(if i.val < 276 then
[488, 849, 777]
else
(if i.val < 277 then
[489, 954, 770]
else
[490, 965, 763]))
else
(if i.val < 279 then
[491, 895, 685]
else
(if i.val < 280 then
[493, 841, 773]
else
[495, 940, 698]))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
[496, 948, 719]
else
[497, 938, 695])
else
(if i.val < 284 then
[498, 856, 736]
else
(if i.val < 285 then
[499, 939, 696]
else
[500, 897, 618])))
else
(if i.val < 289 then
(if i.val < 287 then
[501, 847, 738]
else
(if i.val < 288 then
[503, 974, 789]
else
[504, 976, 768]))
else
(if i.val < 290 then
[505, 871, 697]
else
(if i.val < 291 then
[506, 808, 566]
else
[509, 865, 1072])))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
[510, 961, 779]
else
[511, 870, 701])
else
(if i.val < 295 then
[512, 946, 717]
else
(if i.val < 296 then
[517, 845, 1067]
else
[518, 855, 724])))
else
(if i.val < 300 then
(if i.val < 298 then
[519, 893, 783]
else
(if i.val < 299 then
[520, 955, 731]
else
[525, 943, 709]))
else
(if i.val < 301 then
[526, 859, 591]
else
(if i.val < 302 then
[527, 978, 771]
else
[528, 894, 720]))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
[529, 947, 718]
else
(if i.val < 305 then
[530, 912, 589]
else
[531, 858, 686]))
else
(if i.val < 307 then
[533, 854, 603]
else
(if i.val < 308 then
[535, 936, 689]
else
[536, 876, 782])))
else
(if i.val < 312 then
(if i.val < 310 then
[567, 986, 809]
else
(if i.val < 311 then
[568, 987, 810]
else
[571, 988, 811]))
else
(if i.val < 313 then
[581, 990, 818]
else
(if i.val < 314 then
[585, 1018, 910]
else
[586, 1040, 900]))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
[597, 994, 842]
else
[598, 1027, 883])
else
(if i.val < 318 then
[604, 1009, 916]
else
(if i.val < 319 then
[611, 1041, 884]
else
[620, 1004, 920])))
else
(if i.val < 323 then
(if i.val < 321 then
[688, 1054, 885]
else
(if i.val < 322 then
[690, 1015, 937]
else
[691, 1039, 877]))
else
(if i.val < 324 then
[692, 1031, 860]
else
(if i.val < 325 then
[693, 1011, 896]
else
[702, 1043, 941]))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
[703, 1020, 942]
else
[710, 1014, 944])
else
(if i.val < 329 then
[711, 1029, 945]
else
(if i.val < 330 then
[725, 1013, 951]
else
[726, 996, 846])))
else
(if i.val < 334 then
(if i.val < 332 then
[727, 1044, 952]
else
(if i.val < 333 then
[728, 1022, 953]
else
[733, 1007, 969]))
else
(if i.val < 335 then
[737, 998, 850]
else
(if i.val < 336 then
[759, 1035, 960]
else
[762, 1019, 963])))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
[764, 1055, 901]
else
[765, 1057, 958])
else
(if i.val < 340 then
[767, 1042, 975]
else
(if i.val < 341 then
[772, 1024, 971]
else
[774, 1059, 973])))
else
(if i.val < 345 then
(if i.val < 343 then
[778, 1017, 869]
else
(if i.val < 344 then
[784, 1023, 875]
else
[786, 1025, 898]))
else
(if i.val < 346 then
[787, 1037, 962]
else
(if i.val < 347 then
[788, 1056, 902]
else
[790, 1060, 983]))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
[792, 1062, 979]
else
(if i.val < 350 then
[793, 1063, 981]
else
[862, 1074, 1038]))
else
(if i.val < 352 then
[863, 1070, 1033]
else
(if i.val < 353 then
[956, 1071, 1034]
else
[957, 1069, 1026])))
else
(if i.val < 357 then
(if i.val < 355 then
[964, 1077, 1058]
else
(if i.val < 356 then
[966, 1078, 1045]
else
[967, 1079, 1047]))
else
(if i.val < 358 then
[977, 1075, 1048]
else
(if i.val < 359 then
[980, 1076, 1061]
else
[982, 1073, 1064])))))))))

def g32p_row06_cosetCycles1 : List (List ℕ) :=
  List.ofFn g32p_row06_cosetCycleNodes1

def g32p_row06_cosetMonodromies1 : Fin 360 → Fin 144 :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
0
else
(if i.val < 4 then
0
else
0)))
else
(if i.val < 8 then
(if i.val < 6 then
0
else
(if i.val < 7 then
0
else
0))
else
(if i.val < 9 then
0
else
(if i.val < 10 then
0
else
0))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
0
else
0)
else
(if i.val < 14 then
0
else
(if i.val < 15 then
0
else
0)))
else
(if i.val < 19 then
(if i.val < 17 then
0
else
(if i.val < 18 then
0
else
0))
else
(if i.val < 20 then
0
else
(if i.val < 21 then
0
else
0)))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
0
else
0)
else
(if i.val < 25 then
0
else
(if i.val < 26 then
0
else
0)))
else
(if i.val < 30 then
(if i.val < 28 then
0
else
(if i.val < 29 then
0
else
0))
else
(if i.val < 31 then
0
else
(if i.val < 32 then
0
else
0))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
0
else
(if i.val < 35 then
0
else
0))
else
(if i.val < 37 then
0
else
(if i.val < 38 then
0
else
0)))
else
(if i.val < 42 then
(if i.val < 40 then
0
else
(if i.val < 41 then
0
else
0))
else
(if i.val < 43 then
0
else
(if i.val < 44 then
0
else
0))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
0
else
0)
else
(if i.val < 48 then
0
else
(if i.val < 49 then
0
else
0)))
else
(if i.val < 53 then
(if i.val < 51 then
0
else
(if i.val < 52 then
0
else
0))
else
(if i.val < 54 then
0
else
(if i.val < 55 then
0
else
0))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
0
else
0)
else
(if i.val < 59 then
0
else
(if i.val < 60 then
0
else
0)))
else
(if i.val < 64 then
(if i.val < 62 then
0
else
(if i.val < 63 then
0
else
0))
else
(if i.val < 65 then
0
else
(if i.val < 66 then
0
else
0)))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
0
else
0)
else
(if i.val < 70 then
0
else
(if i.val < 71 then
0
else
0)))
else
(if i.val < 75 then
(if i.val < 73 then
0
else
(if i.val < 74 then
0
else
0))
else
(if i.val < 76 then
0
else
(if i.val < 77 then
0
else
0))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
0
else
(if i.val < 80 then
0
else
0))
else
(if i.val < 82 then
0
else
(if i.val < 83 then
0
else
0)))
else
(if i.val < 87 then
(if i.val < 85 then
0
else
(if i.val < 86 then
0
else
0))
else
(if i.val < 88 then
0
else
(if i.val < 89 then
0
else
0)))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
0
else
0)
else
(if i.val < 93 then
0
else
(if i.val < 94 then
0
else
0)))
else
(if i.val < 98 then
(if i.val < 96 then
0
else
(if i.val < 97 then
0
else
0))
else
(if i.val < 99 then
0
else
(if i.val < 100 then
0
else
0))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
0
else
0)
else
(if i.val < 104 then
0
else
(if i.val < 105 then
0
else
0)))
else
(if i.val < 109 then
(if i.val < 107 then
0
else
(if i.val < 108 then
0
else
0))
else
(if i.val < 110 then
0
else
(if i.val < 111 then
0
else
0)))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
0
else
0)
else
(if i.val < 115 then
0
else
(if i.val < 116 then
0
else
0)))
else
(if i.val < 120 then
(if i.val < 118 then
0
else
(if i.val < 119 then
0
else
0))
else
(if i.val < 121 then
0
else
(if i.val < 122 then
0
else
0))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
0
else
(if i.val < 125 then
0
else
0))
else
(if i.val < 127 then
0
else
(if i.val < 128 then
0
else
0)))
else
(if i.val < 132 then
(if i.val < 130 then
0
else
(if i.val < 131 then
0
else
0))
else
(if i.val < 133 then
0
else
(if i.val < 134 then
0
else
0))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
0
else
0)
else
(if i.val < 138 then
0
else
(if i.val < 139 then
0
else
0)))
else
(if i.val < 143 then
(if i.val < 141 then
0
else
(if i.val < 142 then
0
else
0))
else
(if i.val < 144 then
0
else
(if i.val < 145 then
0
else
0))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
0
else
0)
else
(if i.val < 149 then
0
else
(if i.val < 150 then
0
else
0)))
else
(if i.val < 154 then
(if i.val < 152 then
0
else
(if i.val < 153 then
0
else
0))
else
(if i.val < 155 then
0
else
(if i.val < 156 then
0
else
0)))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
0
else
0)
else
(if i.val < 160 then
0
else
(if i.val < 161 then
0
else
0)))
else
(if i.val < 165 then
(if i.val < 163 then
0
else
(if i.val < 164 then
0
else
0))
else
(if i.val < 166 then
0
else
(if i.val < 167 then
0
else
0))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
0
else
(if i.val < 170 then
0
else
0))
else
(if i.val < 172 then
0
else
(if i.val < 173 then
0
else
0)))
else
(if i.val < 177 then
(if i.val < 175 then
0
else
(if i.val < 176 then
0
else
0))
else
(if i.val < 178 then
0
else
(if i.val < 179 then
0
else
0))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
0
else
0)
else
(if i.val < 183 then
0
else
(if i.val < 184 then
0
else
0)))
else
(if i.val < 188 then
(if i.val < 186 then
0
else
(if i.val < 187 then
0
else
0))
else
(if i.val < 189 then
0
else
(if i.val < 190 then
0
else
0))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
0
else
0)
else
(if i.val < 194 then
0
else
(if i.val < 195 then
0
else
0)))
else
(if i.val < 199 then
(if i.val < 197 then
0
else
(if i.val < 198 then
0
else
0))
else
(if i.val < 200 then
0
else
(if i.val < 201 then
0
else
0)))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
0
else
0)
else
(if i.val < 205 then
0
else
(if i.val < 206 then
0
else
0)))
else
(if i.val < 210 then
(if i.val < 208 then
0
else
(if i.val < 209 then
0
else
0))
else
(if i.val < 211 then
0
else
(if i.val < 212 then
0
else
0))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
0
else
(if i.val < 215 then
0
else
0))
else
(if i.val < 217 then
0
else
(if i.val < 218 then
0
else
0)))
else
(if i.val < 222 then
(if i.val < 220 then
0
else
(if i.val < 221 then
0
else
0))
else
(if i.val < 223 then
0
else
(if i.val < 224 then
0
else
0))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
0
else
0)
else
(if i.val < 228 then
0
else
(if i.val < 229 then
0
else
0)))
else
(if i.val < 233 then
(if i.val < 231 then
0
else
(if i.val < 232 then
0
else
0))
else
(if i.val < 234 then
0
else
(if i.val < 235 then
0
else
0))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
(if i.val < 240 then
0
else
0)))
else
(if i.val < 244 then
(if i.val < 242 then
0
else
(if i.val < 243 then
0
else
0))
else
(if i.val < 245 then
0
else
(if i.val < 246 then
0
else
0)))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
0
else
0)
else
(if i.val < 250 then
0
else
(if i.val < 251 then
0
else
0)))
else
(if i.val < 255 then
(if i.val < 253 then
0
else
(if i.val < 254 then
0
else
0))
else
(if i.val < 256 then
0
else
(if i.val < 257 then
0
else
0))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
0
else
(if i.val < 260 then
0
else
0))
else
(if i.val < 262 then
0
else
(if i.val < 263 then
0
else
0)))
else
(if i.val < 267 then
(if i.val < 265 then
0
else
(if i.val < 266 then
0
else
0))
else
(if i.val < 268 then
0
else
(if i.val < 269 then
0
else
0)))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
0
else
0)
else
(if i.val < 273 then
0
else
(if i.val < 274 then
0
else
0)))
else
(if i.val < 278 then
(if i.val < 276 then
0
else
(if i.val < 277 then
0
else
0))
else
(if i.val < 279 then
0
else
(if i.val < 280 then
0
else
0))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
0
else
0)
else
(if i.val < 284 then
0
else
(if i.val < 285 then
0
else
0)))
else
(if i.val < 289 then
(if i.val < 287 then
0
else
(if i.val < 288 then
0
else
0))
else
(if i.val < 290 then
0
else
(if i.val < 291 then
0
else
0)))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
0
else
0)
else
(if i.val < 295 then
0
else
(if i.val < 296 then
0
else
0)))
else
(if i.val < 300 then
(if i.val < 298 then
0
else
(if i.val < 299 then
0
else
0))
else
(if i.val < 301 then
0
else
(if i.val < 302 then
0
else
0))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
0
else
(if i.val < 305 then
0
else
0))
else
(if i.val < 307 then
0
else
(if i.val < 308 then
0
else
0)))
else
(if i.val < 312 then
(if i.val < 310 then
0
else
(if i.val < 311 then
0
else
0))
else
(if i.val < 313 then
0
else
(if i.val < 314 then
0
else
0))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
0
else
0)
else
(if i.val < 318 then
0
else
(if i.val < 319 then
0
else
0)))
else
(if i.val < 323 then
(if i.val < 321 then
0
else
(if i.val < 322 then
0
else
0))
else
(if i.val < 324 then
0
else
(if i.val < 325 then
0
else
0))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
0
else
0)
else
(if i.val < 329 then
0
else
(if i.val < 330 then
0
else
0)))
else
(if i.val < 334 then
(if i.val < 332 then
0
else
(if i.val < 333 then
0
else
0))
else
(if i.val < 335 then
0
else
(if i.val < 336 then
0
else
0)))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
0
else
0)
else
(if i.val < 340 then
0
else
(if i.val < 341 then
0
else
0)))
else
(if i.val < 345 then
(if i.val < 343 then
0
else
(if i.val < 344 then
0
else
0))
else
(if i.val < 346 then
0
else
(if i.val < 347 then
0
else
0))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
0
else
(if i.val < 350 then
0
else
0))
else
(if i.val < 352 then
0
else
(if i.val < 353 then
0
else
0)))
else
(if i.val < 357 then
(if i.val < 355 then
0
else
(if i.val < 356 then
0
else
0))
else
(if i.val < 358 then
0
else
(if i.val < 359 then
0
else
0)))))))))

def g32p_row06_cosetExponents1 : Fin 360 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 180 then
(if i.val < 90 then
(if i.val < 45 then
(if i.val < 22 then
(if i.val < 11 then
(if i.val < 5 then
(if i.val < 2 then
(if i.val < 1 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 3 then
Multiplicative.ofAdd 0
else
(if i.val < 4 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 8 then
(if i.val < 6 then
Multiplicative.ofAdd 0
else
(if i.val < 7 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 9 then
Multiplicative.ofAdd 0
else
(if i.val < 10 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 16 then
(if i.val < 13 then
(if i.val < 12 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 14 then
Multiplicative.ofAdd 0
else
(if i.val < 15 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 19 then
(if i.val < 17 then
Multiplicative.ofAdd 0
else
(if i.val < 18 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 20 then
Multiplicative.ofAdd 0
else
(if i.val < 21 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 33 then
(if i.val < 27 then
(if i.val < 24 then
(if i.val < 23 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 25 then
Multiplicative.ofAdd 0
else
(if i.val < 26 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 30 then
(if i.val < 28 then
Multiplicative.ofAdd 0
else
(if i.val < 29 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 31 then
Multiplicative.ofAdd 0
else
(if i.val < 32 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 39 then
(if i.val < 36 then
(if i.val < 34 then
Multiplicative.ofAdd 0
else
(if i.val < 35 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 37 then
Multiplicative.ofAdd 0
else
(if i.val < 38 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 42 then
(if i.val < 40 then
Multiplicative.ofAdd 0
else
(if i.val < 41 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 43 then
Multiplicative.ofAdd 0
else
(if i.val < 44 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 67 then
(if i.val < 56 then
(if i.val < 50 then
(if i.val < 47 then
(if i.val < 46 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 48 then
Multiplicative.ofAdd 0
else
(if i.val < 49 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 53 then
(if i.val < 51 then
Multiplicative.ofAdd 0
else
(if i.val < 52 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 54 then
Multiplicative.ofAdd 0
else
(if i.val < 55 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 61 then
(if i.val < 58 then
(if i.val < 57 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 59 then
Multiplicative.ofAdd 0
else
(if i.val < 60 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 64 then
(if i.val < 62 then
Multiplicative.ofAdd 0
else
(if i.val < 63 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 65 then
Multiplicative.ofAdd 0
else
(if i.val < 66 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 78 then
(if i.val < 72 then
(if i.val < 69 then
(if i.val < 68 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 70 then
Multiplicative.ofAdd 0
else
(if i.val < 71 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 75 then
(if i.val < 73 then
Multiplicative.ofAdd 0
else
(if i.val < 74 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 76 then
Multiplicative.ofAdd 0
else
(if i.val < 77 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 84 then
(if i.val < 81 then
(if i.val < 79 then
Multiplicative.ofAdd 0
else
(if i.val < 80 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 82 then
Multiplicative.ofAdd 0
else
(if i.val < 83 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 87 then
(if i.val < 85 then
Multiplicative.ofAdd 0
else
(if i.val < 86 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 88 then
Multiplicative.ofAdd 0
else
(if i.val < 89 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))
else
(if i.val < 135 then
(if i.val < 112 then
(if i.val < 101 then
(if i.val < 95 then
(if i.val < 92 then
(if i.val < 91 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 93 then
Multiplicative.ofAdd 0
else
(if i.val < 94 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 98 then
(if i.val < 96 then
Multiplicative.ofAdd 0
else
(if i.val < 97 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 99 then
Multiplicative.ofAdd 0
else
(if i.val < 100 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 106 then
(if i.val < 103 then
(if i.val < 102 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 104 then
Multiplicative.ofAdd 0
else
(if i.val < 105 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 109 then
(if i.val < 107 then
Multiplicative.ofAdd 0
else
(if i.val < 108 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 110 then
Multiplicative.ofAdd 0
else
(if i.val < 111 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 123 then
(if i.val < 117 then
(if i.val < 114 then
(if i.val < 113 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 115 then
Multiplicative.ofAdd 0
else
(if i.val < 116 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 120 then
(if i.val < 118 then
Multiplicative.ofAdd 0
else
(if i.val < 119 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 121 then
Multiplicative.ofAdd 0
else
(if i.val < 122 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 129 then
(if i.val < 126 then
(if i.val < 124 then
Multiplicative.ofAdd 0
else
(if i.val < 125 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 127 then
Multiplicative.ofAdd 0
else
(if i.val < 128 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 132 then
(if i.val < 130 then
Multiplicative.ofAdd 0
else
(if i.val < 131 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 133 then
Multiplicative.ofAdd 0
else
(if i.val < 134 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 157 then
(if i.val < 146 then
(if i.val < 140 then
(if i.val < 137 then
(if i.val < 136 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 138 then
Multiplicative.ofAdd 0
else
(if i.val < 139 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 143 then
(if i.val < 141 then
Multiplicative.ofAdd 0
else
(if i.val < 142 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 144 then
Multiplicative.ofAdd 0
else
(if i.val < 145 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 151 then
(if i.val < 148 then
(if i.val < 147 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 149 then
Multiplicative.ofAdd 0
else
(if i.val < 150 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 154 then
(if i.val < 152 then
Multiplicative.ofAdd 0
else
(if i.val < 153 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 155 then
Multiplicative.ofAdd 0
else
(if i.val < 156 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 168 then
(if i.val < 162 then
(if i.val < 159 then
(if i.val < 158 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 160 then
Multiplicative.ofAdd 0
else
(if i.val < 161 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 165 then
(if i.val < 163 then
Multiplicative.ofAdd 0
else
(if i.val < 164 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 166 then
Multiplicative.ofAdd 0
else
(if i.val < 167 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 174 then
(if i.val < 171 then
(if i.val < 169 then
Multiplicative.ofAdd 0
else
(if i.val < 170 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 172 then
Multiplicative.ofAdd 0
else
(if i.val < 173 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 177 then
(if i.val < 175 then
Multiplicative.ofAdd 0
else
(if i.val < 176 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 178 then
Multiplicative.ofAdd 0
else
(if i.val < 179 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))))
else
(if i.val < 270 then
(if i.val < 225 then
(if i.val < 202 then
(if i.val < 191 then
(if i.val < 185 then
(if i.val < 182 then
(if i.val < 181 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 183 then
Multiplicative.ofAdd 0
else
(if i.val < 184 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 188 then
(if i.val < 186 then
Multiplicative.ofAdd 0
else
(if i.val < 187 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 189 then
Multiplicative.ofAdd 0
else
(if i.val < 190 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 196 then
(if i.val < 193 then
(if i.val < 192 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 194 then
Multiplicative.ofAdd 0
else
(if i.val < 195 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 199 then
(if i.val < 197 then
Multiplicative.ofAdd 0
else
(if i.val < 198 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 200 then
Multiplicative.ofAdd 0
else
(if i.val < 201 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 213 then
(if i.val < 207 then
(if i.val < 204 then
(if i.val < 203 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 205 then
Multiplicative.ofAdd 0
else
(if i.val < 206 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 210 then
(if i.val < 208 then
Multiplicative.ofAdd 0
else
(if i.val < 209 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 211 then
Multiplicative.ofAdd 0
else
(if i.val < 212 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 219 then
(if i.val < 216 then
(if i.val < 214 then
Multiplicative.ofAdd 0
else
(if i.val < 215 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 217 then
Multiplicative.ofAdd 0
else
(if i.val < 218 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 222 then
(if i.val < 220 then
Multiplicative.ofAdd 0
else
(if i.val < 221 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 223 then
Multiplicative.ofAdd 0
else
(if i.val < 224 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 247 then
(if i.val < 236 then
(if i.val < 230 then
(if i.val < 227 then
(if i.val < 226 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 228 then
Multiplicative.ofAdd 0
else
(if i.val < 229 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 233 then
(if i.val < 231 then
Multiplicative.ofAdd 0
else
(if i.val < 232 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 234 then
Multiplicative.ofAdd 0
else
(if i.val < 235 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 241 then
(if i.val < 238 then
(if i.val < 237 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 239 then
Multiplicative.ofAdd 0
else
(if i.val < 240 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 244 then
(if i.val < 242 then
Multiplicative.ofAdd 0
else
(if i.val < 243 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 245 then
Multiplicative.ofAdd 0
else
(if i.val < 246 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 258 then
(if i.val < 252 then
(if i.val < 249 then
(if i.val < 248 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 250 then
Multiplicative.ofAdd 0
else
(if i.val < 251 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 255 then
(if i.val < 253 then
Multiplicative.ofAdd 0
else
(if i.val < 254 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 256 then
Multiplicative.ofAdd 0
else
(if i.val < 257 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 264 then
(if i.val < 261 then
(if i.val < 259 then
Multiplicative.ofAdd 0
else
(if i.val < 260 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 262 then
Multiplicative.ofAdd 0
else
(if i.val < 263 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 267 then
(if i.val < 265 then
Multiplicative.ofAdd 0
else
(if i.val < 266 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 268 then
Multiplicative.ofAdd 0
else
(if i.val < 269 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))
else
(if i.val < 315 then
(if i.val < 292 then
(if i.val < 281 then
(if i.val < 275 then
(if i.val < 272 then
(if i.val < 271 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 273 then
Multiplicative.ofAdd 0
else
(if i.val < 274 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 278 then
(if i.val < 276 then
Multiplicative.ofAdd 0
else
(if i.val < 277 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 279 then
Multiplicative.ofAdd 0
else
(if i.val < 280 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 286 then
(if i.val < 283 then
(if i.val < 282 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 284 then
Multiplicative.ofAdd 0
else
(if i.val < 285 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 289 then
(if i.val < 287 then
Multiplicative.ofAdd 0
else
(if i.val < 288 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 290 then
Multiplicative.ofAdd 0
else
(if i.val < 291 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 303 then
(if i.val < 297 then
(if i.val < 294 then
(if i.val < 293 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 295 then
Multiplicative.ofAdd 0
else
(if i.val < 296 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 300 then
(if i.val < 298 then
Multiplicative.ofAdd 0
else
(if i.val < 299 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 301 then
Multiplicative.ofAdd 0
else
(if i.val < 302 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 309 then
(if i.val < 306 then
(if i.val < 304 then
Multiplicative.ofAdd 0
else
(if i.val < 305 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 307 then
Multiplicative.ofAdd 0
else
(if i.val < 308 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 312 then
(if i.val < 310 then
Multiplicative.ofAdd 0
else
(if i.val < 311 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 313 then
Multiplicative.ofAdd 0
else
(if i.val < 314 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 337 then
(if i.val < 326 then
(if i.val < 320 then
(if i.val < 317 then
(if i.val < 316 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 318 then
Multiplicative.ofAdd 0
else
(if i.val < 319 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 323 then
(if i.val < 321 then
Multiplicative.ofAdd 0
else
(if i.val < 322 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 324 then
Multiplicative.ofAdd 0
else
(if i.val < 325 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 331 then
(if i.val < 328 then
(if i.val < 327 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 329 then
Multiplicative.ofAdd 0
else
(if i.val < 330 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 334 then
(if i.val < 332 then
Multiplicative.ofAdd 0
else
(if i.val < 333 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 335 then
Multiplicative.ofAdd 0
else
(if i.val < 336 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 348 then
(if i.val < 342 then
(if i.val < 339 then
(if i.val < 338 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 340 then
Multiplicative.ofAdd 0
else
(if i.val < 341 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 345 then
(if i.val < 343 then
Multiplicative.ofAdd 0
else
(if i.val < 344 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 346 then
Multiplicative.ofAdd 0
else
(if i.val < 347 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 354 then
(if i.val < 351 then
(if i.val < 349 then
Multiplicative.ofAdd 0
else
(if i.val < 350 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 352 then
Multiplicative.ofAdd 0
else
(if i.val < 353 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 357 then
(if i.val < 355 then
Multiplicative.ofAdd 0
else
(if i.val < 356 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 358 then
Multiplicative.ofAdd 0
else
(if i.val < 359 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))))

def g32p_row06_cosetLabels2 : Fin 1080 → Fin 552 :=
  fun i => (if i.val < 540 then
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
1)
else
(if i.val < 3 then
2
else
3))
else
(if i.val < 6 then
(if i.val < 5 then
4
else
5)
else
(if i.val < 7 then
6
else
7)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
8
else
9)
else
(if i.val < 11 then
10
else
11))
else
(if i.val < 14 then
(if i.val < 13 then
12
else
13)
else
(if i.val < 15 then
14
else
15))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
16
else
17)
else
(if i.val < 19 then
18
else
19))
else
(if i.val < 22 then
(if i.val < 21 then
20
else
21)
else
(if i.val < 23 then
22
else
23)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
24
else
25)
else
(if i.val < 27 then
26
else
27))
else
(if i.val < 30 then
(if i.val < 29 then
28
else
29)
else
(if i.val < 31 then
30
else
(if i.val < 32 then
31
else
32))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
33
else
34)
else
(if i.val < 36 then
35
else
36))
else
(if i.val < 39 then
(if i.val < 38 then
37
else
38)
else
(if i.val < 40 then
39
else
40)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
41
else
42)
else
(if i.val < 44 then
43
else
44))
else
(if i.val < 47 then
(if i.val < 46 then
45
else
46)
else
(if i.val < 48 then
47
else
(if i.val < 49 then
48
else
49)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
50
else
51)
else
(if i.val < 53 then
52
else
53))
else
(if i.val < 56 then
(if i.val < 55 then
46
else
54)
else
(if i.val < 57 then
55
else
56)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
57
else
58)
else
(if i.val < 61 then
59
else
56))
else
(if i.val < 64 then
(if i.val < 63 then
60
else
61)
else
(if i.val < 65 then
62
else
(if i.val < 66 then
63
else
64)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
65
else
66)
else
(if i.val < 70 then
67
else
68))
else
(if i.val < 73 then
(if i.val < 72 then
69
else
70)
else
(if i.val < 74 then
71
else
72)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
73
else
74)
else
(if i.val < 78 then
75
else
76))
else
(if i.val < 81 then
(if i.val < 80 then
77
else
78)
else
(if i.val < 82 then
79
else
(if i.val < 83 then
80
else
81)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
63
else
82)
else
(if i.val < 87 then
83
else
84))
else
(if i.val < 90 then
(if i.val < 89 then
85
else
86)
else
(if i.val < 91 then
87
else
88)))
else
(if i.val < 96 then
(if i.val < 94 then
(if i.val < 93 then
59
else
89)
else
(if i.val < 95 then
90
else
91))
else
(if i.val < 98 then
(if i.val < 97 then
4
else
92)
else
(if i.val < 99 then
93
else
(if i.val < 100 then
76
else
94))))))
else
(if i.val < 118 then
(if i.val < 109 then
(if i.val < 105 then
(if i.val < 103 then
(if i.val < 102 then
95
else
54)
else
(if i.val < 104 then
96
else
97))
else
(if i.val < 107 then
(if i.val < 106 then
98
else
99)
else
(if i.val < 108 then
100
else
82)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
75
else
101)
else
(if i.val < 112 then
102
else
103))
else
(if i.val < 115 then
(if i.val < 114 then
100
else
104)
else
(if i.val < 116 then
105
else
(if i.val < 117 then
106
else
98)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
107
else
108)
else
(if i.val < 121 then
109
else
110))
else
(if i.val < 124 then
(if i.val < 123 then
111
else
112)
else
(if i.val < 125 then
113
else
81)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
58
else
114)
else
(if i.val < 129 then
115
else
116))
else
(if i.val < 132 then
(if i.val < 131 then
71
else
117)
else
(if i.val < 133 then
118
else
(if i.val < 134 then
119
else
120))))))))
else
(if i.val < 202 then
(if i.val < 168 then
(if i.val < 151 then
(if i.val < 143 then
(if i.val < 139 then
(if i.val < 137 then
(if i.val < 136 then
121
else
122)
else
(if i.val < 138 then
123
else
124))
else
(if i.val < 141 then
(if i.val < 140 then
125
else
126)
else
(if i.val < 142 then
127
else
128)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
129
else
130)
else
(if i.val < 146 then
131
else
132))
else
(if i.val < 149 then
(if i.val < 148 then
133
else
8)
else
(if i.val < 150 then
134
else
135))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
136
else
137)
else
(if i.val < 154 then
138
else
9))
else
(if i.val < 157 then
(if i.val < 156 then
139
else
140)
else
(if i.val < 158 then
141
else
142)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
7
else
143)
else
(if i.val < 162 then
144
else
145))
else
(if i.val < 165 then
(if i.val < 164 then
146
else
147)
else
(if i.val < 166 then
148
else
(if i.val < 167 then
149
else
150))))))
else
(if i.val < 185 then
(if i.val < 176 then
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
151
else
152)
else
(if i.val < 171 then
153
else
16))
else
(if i.val < 174 then
(if i.val < 173 then
154
else
155)
else
(if i.val < 175 then
156
else
157)))
else
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
158
else
159)
else
(if i.val < 179 then
160
else
161))
else
(if i.val < 182 then
(if i.val < 181 then
162
else
163)
else
(if i.val < 183 then
164
else
(if i.val < 184 then
165
else
166)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
167
else
132)
else
(if i.val < 188 then
168
else
169))
else
(if i.val < 191 then
(if i.val < 190 then
170
else
171)
else
(if i.val < 192 then
133
else
172)))
else
(if i.val < 197 then
(if i.val < 195 then
(if i.val < 194 then
173
else
174)
else
(if i.val < 196 then
175
else
176))
else
(if i.val < 199 then
(if i.val < 198 then
177
else
146)
else
(if i.val < 200 then
178
else
(if i.val < 201 then
179
else
180)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
181
else
182)
else
(if i.val < 205 then
183
else
184))
else
(if i.val < 208 then
(if i.val < 207 then
185
else
186)
else
(if i.val < 209 then
141
else
187)))
else
(if i.val < 214 then
(if i.val < 212 then
(if i.val < 211 then
188
else
189)
else
(if i.val < 213 then
190
else
191))
else
(if i.val < 216 then
(if i.val < 215 then
192
else
193)
else
(if i.val < 217 then
194
else
(if i.val < 218 then
148
else
143)))))
else
(if i.val < 227 then
(if i.val < 223 then
(if i.val < 221 then
(if i.val < 220 then
195
else
196)
else
(if i.val < 222 then
197
else
198))
else
(if i.val < 225 then
(if i.val < 224 then
10
else
199)
else
(if i.val < 226 then
200
else
201)))
else
(if i.val < 231 then
(if i.val < 229 then
(if i.val < 228 then
15
else
202)
else
(if i.val < 230 then
203
else
204))
else
(if i.val < 233 then
(if i.val < 232 then
205
else
206)
else
(if i.val < 234 then
207
else
(if i.val < 235 then
208
else
172))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
209
else
210)
else
(if i.val < 239 then
211
else
18))
else
(if i.val < 242 then
(if i.val < 241 then
212
else
213)
else
(if i.val < 243 then
194
else
214)))
else
(if i.val < 248 then
(if i.val < 246 then
(if i.val < 245 then
150
else
215)
else
(if i.val < 247 then
208
else
151))
else
(if i.val < 250 then
(if i.val < 249 then
216
else
217)
else
(if i.val < 251 then
218
else
(if i.val < 252 then
219
else
220)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
145
else
156)
else
(if i.val < 256 then
221
else
222))
else
(if i.val < 259 then
(if i.val < 258 then
223
else
183)
else
(if i.val < 260 then
224
else
225)))
else
(if i.val < 265 then
(if i.val < 263 then
(if i.val < 262 then
154
else
226)
else
(if i.val < 264 then
170
else
212))
else
(if i.val < 267 then
(if i.val < 266 then
227
else
226)
else
(if i.val < 268 then
147
else
(if i.val < 269 then
195
else
228)))))))))
else
(if i.val < 405 then
(if i.val < 337 then
(if i.val < 303 then
(if i.val < 286 then
(if i.val < 278 then
(if i.val < 274 then
(if i.val < 272 then
(if i.val < 271 then
229
else
230)
else
(if i.val < 273 then
231
else
131))
else
(if i.val < 276 then
(if i.val < 275 then
232
else
233)
else
(if i.val < 277 then
192
else
203)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
234
else
235)
else
(if i.val < 281 then
14
else
236))
else
(if i.val < 284 then
(if i.val < 283 then
237
else
193)
else
(if i.val < 285 then
238
else
12))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
239
else
240)
else
(if i.val < 289 then
197
else
218))
else
(if i.val < 292 then
(if i.val < 291 then
163
else
130)
else
(if i.val < 293 then
223
else
241)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
242
else
243)
else
(if i.val < 297 then
244
else
245))
else
(if i.val < 300 then
(if i.val < 299 then
246
else
247)
else
(if i.val < 301 then
248
else
(if i.val < 302 then
249
else
250))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
251
else
249)
else
(if i.val < 306 then
252
else
253))
else
(if i.val < 309 then
(if i.val < 308 then
254
else
255)
else
(if i.val < 310 then
256
else
29)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
257
else
258)
else
(if i.val < 314 then
259
else
260))
else
(if i.val < 317 then
(if i.val < 316 then
261
else
262)
else
(if i.val < 318 then
263
else
(if i.val < 319 then
264
else
265)))))
else
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
266
else
253)
else
(if i.val < 323 then
267
else
268))
else
(if i.val < 326 then
(if i.val < 325 then
269
else
270)
else
(if i.val < 327 then
271
else
272)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
273
else
274)
else
(if i.val < 331 then
275
else
276))
else
(if i.val < 334 then
(if i.val < 333 then
277
else
278)
else
(if i.val < 335 then
24
else
(if i.val < 336 then
279
else
280)))))))
else
(if i.val < 371 then
(if i.val < 354 then
(if i.val < 345 then
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
260
else
281)
else
(if i.val < 340 then
282
else
283))
else
(if i.val < 343 then
(if i.val < 342 then
284
else
285)
else
(if i.val < 344 then
286
else
287)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
288
else
289)
else
(if i.val < 348 then
26
else
290))
else
(if i.val < 351 then
(if i.val < 350 then
291
else
269)
else
(if i.val < 352 then
292
else
(if i.val < 353 then
293
else
294)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
295
else
296)
else
(if i.val < 357 then
44
else
297))
else
(if i.val < 360 then
(if i.val < 359 then
298
else
299)
else
(if i.val < 361 then
300
else
301)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
302
else
303)
else
(if i.val < 365 then
304
else
305))
else
(if i.val < 368 then
(if i.val < 367 then
306
else
51)
else
(if i.val < 369 then
251
else
(if i.val < 370 then
307
else
308))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
309
else
310)
else
(if i.val < 374 then
311
else
259))
else
(if i.val < 377 then
(if i.val < 376 then
312
else
258)
else
(if i.val < 378 then
313
else
314)))
else
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
315
else
21)
else
(if i.val < 382 then
316
else
317))
else
(if i.val < 385 then
(if i.val < 384 then
270
else
318)
else
(if i.val < 386 then
319
else
(if i.val < 387 then
284
else
254)))))
else
(if i.val < 396 then
(if i.val < 392 then
(if i.val < 390 then
(if i.val < 389 then
320
else
316)
else
(if i.val < 391 then
321
else
283))
else
(if i.val < 394 then
(if i.val < 393 then
322
else
268)
else
(if i.val < 395 then
323
else
324)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
325
else
326)
else
(if i.val < 399 then
327
else
328))
else
(if i.val < 402 then
(if i.val < 401 then
329
else
330)
else
(if i.val < 403 then
308
else
(if i.val < 404 then
331
else
332))))))))
else
(if i.val < 472 then
(if i.val < 438 then
(if i.val < 421 then
(if i.val < 413 then
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
333
else
334)
else
(if i.val < 408 then
335
else
291))
else
(if i.val < 411 then
(if i.val < 410 then
336
else
275)
else
(if i.val < 412 then
337
else
338)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
247
else
292)
else
(if i.val < 416 then
339
else
34))
else
(if i.val < 419 then
(if i.val < 418 then
340
else
341)
else
(if i.val < 420 then
342
else
343))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
22
else
25)
else
(if i.val < 424 then
20
else
52))
else
(if i.val < 427 then
(if i.val < 426 then
331
else
344)
else
(if i.val < 428 then
345
else
325)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
53
else
346)
else
(if i.val < 432 then
347
else
335))
else
(if i.val < 435 then
(if i.val < 434 then
264
else
337)
else
(if i.val < 436 then
348
else
(if i.val < 437 then
271
else
349))))))
else
(if i.val < 455 then
(if i.val < 446 then
(if i.val < 442 then
(if i.val < 440 then
(if i.val < 439 then
319
else
350)
else
(if i.val < 441 then
288
else
322))
else
(if i.val < 444 then
(if i.val < 443 then
294
else
41)
else
(if i.val < 445 then
0
else
277)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
351
else
298)
else
(if i.val < 449 then
38
else
28))
else
(if i.val < 452 then
(if i.val < 451 then
273
else
33)
else
(if i.val < 453 then
19
else
(if i.val < 454 then
352
else
332)))))
else
(if i.val < 463 then
(if i.val < 459 then
(if i.val < 457 then
(if i.val < 456 then
353
else
49)
else
(if i.val < 458 then
348
else
354))
else
(if i.val < 461 then
(if i.val < 460 then
355
else
341)
else
(if i.val < 462 then
350
else
272)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
356
else
357)
else
(if i.val < 466 then
358
else
359))
else
(if i.val < 469 then
(if i.val < 468 then
42
else
360)
else
(if i.val < 470 then
361
else
(if i.val < 471 then
267
else
362)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
361
else
40)
else
(if i.val < 475 then
48
else
363))
else
(if i.val < 478 then
(if i.val < 477 then
355
else
243)
else
(if i.val < 479 then
330
else
364)))
else
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
358
else
365)
else
(if i.val < 483 then
352
else
366))
else
(if i.val < 486 then
(if i.val < 485 then
278
else
367)
else
(if i.val < 487 then
289
else
(if i.val < 488 then
333
else
250)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
349
else
317)
else
(if i.val < 492 then
23
else
302))
else
(if i.val < 495 then
(if i.val < 494 then
345
else
368)
else
(if i.val < 496 then
354
else
326)))
else
(if i.val < 501 then
(if i.val < 499 then
(if i.val < 498 then
364
else
353)
else
(if i.val < 500 then
369
else
43))
else
(if i.val < 503 then
(if i.val < 502 then
279
else
290)
else
(if i.val < 504 then
296
else
(if i.val < 505 then
366
else
257))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
370
else
338)
else
(if i.val < 509 then
371
else
328))
else
(if i.val < 512 then
(if i.val < 511 then
286
else
359)
else
(if i.val < 513 then
372
else
50)))
else
(if i.val < 518 then
(if i.val < 516 then
(if i.val < 515 then
363
else
287)
else
(if i.val < 517 then
368
else
281))
else
(if i.val < 520 then
(if i.val < 519 then
362
else
373)
else
(if i.val < 521 then
374
else
(if i.val < 522 then
252
else
375)))))
else
(if i.val < 531 then
(if i.val < 527 then
(if i.val < 525 then
(if i.val < 524 then
376
else
300)
else
(if i.val < 526 then
244
else
276))
else
(if i.val < 529 then
(if i.val < 528 then
245
else
305)
else
(if i.val < 530 then
377
else
255)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
360
else
378)
else
(if i.val < 534 then
379
else
39))
else
(if i.val < 537 then
(if i.val < 536 then
314
else
380)
else
(if i.val < 538 then
381
else
(if i.val < 539 then
382
else
383))))))))))
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
384
else
385)
else
(if i.val < 543 then
386
else
387))
else
(if i.val < 546 then
(if i.val < 545 then
388
else
389)
else
(if i.val < 547 then
2
else
390)))
else
(if i.val < 552 then
(if i.val < 550 then
(if i.val < 549 then
391
else
392)
else
(if i.val < 551 then
393
else
394))
else
(if i.val < 554 then
(if i.val < 553 then
395
else
114)
else
(if i.val < 555 then
396
else
397))))
else
(if i.val < 564 then
(if i.val < 560 then
(if i.val < 558 then
(if i.val < 557 then
398
else
84)
else
(if i.val < 559 then
399
else
400))
else
(if i.val < 562 then
(if i.val < 561 then
73
else
401)
else
(if i.val < 563 then
402
else
403)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
404
else
405)
else
(if i.val < 567 then
1
else
395))
else
(if i.val < 570 then
(if i.val < 569 then
406
else
396)
else
(if i.val < 571 then
407
else
(if i.val < 572 then
90
else
408))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
80
else
120)
else
(if i.val < 576 then
409
else
83))
else
(if i.val < 579 then
(if i.val < 578 then
410
else
411)
else
(if i.val < 580 then
412
else
413)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
414
else
415)
else
(if i.val < 584 then
416
else
417))
else
(if i.val < 587 then
(if i.val < 586 then
418
else
419)
else
(if i.val < 588 then
420
else
(if i.val < 589 then
421
else
422)))))
else
(if i.val < 598 then
(if i.val < 594 then
(if i.val < 592 then
(if i.val < 591 then
423
else
108)
else
(if i.val < 593 then
424
else
425))
else
(if i.val < 596 then
(if i.val < 595 then
426
else
427)
else
(if i.val < 597 then
425
else
428)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
429
else
430)
else
(if i.val < 601 then
431
else
432))
else
(if i.val < 604 then
(if i.val < 603 then
67
else
433)
else
(if i.val < 605 then
434
else
(if i.val < 606 then
435
else
435)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
70
else
111)
else
(if i.val < 610 then
436
else
437))
else
(if i.val < 613 then
(if i.val < 612 then
390
else
415)
else
(if i.val < 614 then
438
else
439)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
440
else
441)
else
(if i.val < 618 then
442
else
443))
else
(if i.val < 621 then
(if i.val < 620 then
78
else
444)
else
(if i.val < 622 then
440
else
(if i.val < 623 then
403
else
399)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
445
else
113)
else
(if i.val < 627 then
397
else
392))
else
(if i.val < 630 then
(if i.val < 629 then
446
else
62)
else
(if i.val < 631 then
447
else
447)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
61
else
448)
else
(if i.val < 635 then
402
else
409))
else
(if i.val < 638 then
(if i.val < 637 then
423
else
449)
else
(if i.val < 639 then
450
else
(if i.val < 640 then
105
else
427))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
451
else
68)
else
(if i.val < 644 then
452
else
453))
else
(if i.val < 647 then
(if i.val < 646 then
421
else
88)
else
(if i.val < 648 then
452
else
91)))
else
(if i.val < 653 then
(if i.val < 651 then
(if i.val < 650 then
55
else
454)
else
(if i.val < 652 then
455
else
102))
else
(if i.val < 655 then
(if i.val < 654 then
122
else
429)
else
(if i.val < 656 then
456
else
(if i.val < 657 then
457
else
458)))))
else
(if i.val < 666 then
(if i.val < 662 then
(if i.val < 660 then
(if i.val < 659 then
459
else
408)
else
(if i.val < 661 then
412
else
460))
else
(if i.val < 664 then
(if i.val < 663 then
461
else
74)
else
(if i.val < 665 then
462
else
463)))
else
(if i.val < 670 then
(if i.val < 668 then
(if i.val < 667 then
438
else
464)
else
(if i.val < 669 then
65
else
465))
else
(if i.val < 672 then
(if i.val < 671 then
466
else
467)
else
(if i.val < 673 then
458
else
(if i.val < 674 then
411
else
424))))))))
else
(if i.val < 742 then
(if i.val < 708 then
(if i.val < 691 then
(if i.val < 683 then
(if i.val < 679 then
(if i.val < 677 then
(if i.val < 676 then
406
else
468)
else
(if i.val < 678 then
469
else
398))
else
(if i.val < 681 then
(if i.val < 680 then
404
else
414)
else
(if i.val < 682 then
405
else
470)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
471
else
472)
else
(if i.val < 686 then
473
else
474))
else
(if i.val < 689 then
(if i.val < 688 then
85
else
418)
else
(if i.val < 690 then
472
else
475))))
else
(if i.val < 699 then
(if i.val < 695 then
(if i.val < 693 then
(if i.val < 692 then
454
else
476)
else
(if i.val < 694 then
428
else
112))
else
(if i.val < 697 then
(if i.val < 696 then
57
else
386)
else
(if i.val < 698 then
97
else
477)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
123
else
383)
else
(if i.val < 702 then
401
else
410))
else
(if i.val < 705 then
(if i.val < 704 then
477
else
416)
else
(if i.val < 706 then
87
else
(if i.val < 707 then
391
else
478))))))
else
(if i.val < 725 then
(if i.val < 716 then
(if i.val < 712 then
(if i.val < 710 then
(if i.val < 709 then
109
else
448)
else
(if i.val < 711 then
479
else
417))
else
(if i.val < 714 then
(if i.val < 713 then
72
else
96)
else
(if i.val < 715 then
106
else
60)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
469
else
94)
else
(if i.val < 719 then
437
else
449))
else
(if i.val < 722 then
(if i.val < 721 then
388
else
426)
else
(if i.val < 723 then
480
else
(if i.val < 724 then
86
else
413)))))
else
(if i.val < 733 then
(if i.val < 729 then
(if i.val < 727 then
(if i.val < 726 then
481
else
445)
else
(if i.val < 728 then
92
else
434))
else
(if i.val < 731 then
(if i.val < 730 then
79
else
482)
else
(if i.val < 732 then
419
else
483)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
451
else
475)
else
(if i.val < 736 then
465
else
385))
else
(if i.val < 739 then
(if i.val < 738 then
430
else
394)
else
(if i.val < 740 then
484
else
(if i.val < 741 then
104
else
382)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
443
else
442)
else
(if i.val < 745 then
101
else
89))
else
(if i.val < 748 then
(if i.val < 747 then
455
else
66)
else
(if i.val < 749 then
400
else
462)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
110
else
481)
else
(if i.val < 753 then
439
else
482))
else
(if i.val < 756 then
(if i.val < 755 then
422
else
485)
else
(if i.val < 757 then
64
else
(if i.val < 758 then
486
else
487)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
436
else
95)
else
(if i.val < 762 then
446
else
488))
else
(if i.val < 765 then
(if i.val < 764 then
115
else
480)
else
(if i.val < 766 then
389
else
450)))
else
(if i.val < 771 then
(if i.val < 769 then
(if i.val < 768 then
488
else
99)
else
(if i.val < 770 then
444
else
407))
else
(if i.val < 773 then
(if i.val < 772 then
470
else
479)
else
(if i.val < 774 then
121
else
(if i.val < 775 then
393
else
460))))))
else
(if i.val < 793 then
(if i.val < 784 then
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
117
else
464)
else
(if i.val < 779 then
431
else
3))
else
(if i.val < 782 then
(if i.val < 781 then
467
else
489)
else
(if i.val < 783 then
490
else
478)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
118
else
486)
else
(if i.val < 787 then
103
else
461))
else
(if i.val < 790 then
(if i.val < 789 then
381
else
476)
else
(if i.val < 791 then
93
else
(if i.val < 792 then
116
else
489)))))
else
(if i.val < 801 then
(if i.val < 797 then
(if i.val < 795 then
(if i.val < 794 then
69
else
474)
else
(if i.val < 796 then
491
else
167))
else
(if i.val < 799 then
(if i.val < 798 then
492
else
236)
else
(if i.val < 800 then
238
else
493)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
494
else
495)
else
(if i.val < 804 then
496
else
187))
else
(if i.val < 807 then
(if i.val < 806 then
497
else
498)
else
(if i.val < 808 then
499
else
(if i.val < 809 then
500
else
501)))))))))
else
(if i.val < 945 then
(if i.val < 877 then
(if i.val < 843 then
(if i.val < 826 then
(if i.val < 818 then
(if i.val < 814 then
(if i.val < 812 then
(if i.val < 811 then
161
else
502)
else
(if i.val < 813 then
503
else
504))
else
(if i.val < 816 then
(if i.val < 815 then
505
else
179)
else
(if i.val < 817 then
233
else
506)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
196
else
507)
else
(if i.val < 821 then
508
else
509))
else
(if i.val < 824 then
(if i.val < 823 then
221
else
510)
else
(if i.val < 825 then
511
else
237))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
177
else
219)
else
(if i.val < 829 then
512
else
513))
else
(if i.val < 832 then
(if i.val < 831 then
514
else
515)
else
(if i.val < 833 then
516
else
152)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
517
else
239)
else
(if i.val < 837 then
199
else
518))
else
(if i.val < 840 then
(if i.val < 839 then
222
else
162)
else
(if i.val < 841 then
157
else
(if i.val < 842 then
135
else
175))))))
else
(if i.val < 860 then
(if i.val < 851 then
(if i.val < 847 then
(if i.val < 845 then
(if i.val < 844 then
511
else
508)
else
(if i.val < 846 then
202
else
515))
else
(if i.val < 849 then
(if i.val < 848 then
216
else
242)
else
(if i.val < 850 then
171
else
191)))
else
(if i.val < 855 then
(if i.val < 853 then
(if i.val < 852 then
213
else
519)
else
(if i.val < 854 then
180
else
139))
else
(if i.val < 857 then
(if i.val < 856 then
520
else
220)
else
(if i.val < 858 then
494
else
(if i.val < 859 then
521
else
138)))))
else
(if i.val < 868 then
(if i.val < 864 then
(if i.val < 862 then
(if i.val < 861 then
512
else
522)
else
(if i.val < 863 then
523
else
214))
else
(if i.val < 866 then
(if i.val < 865 then
125
else
144)
else
(if i.val < 867 then
524
else
211)))
else
(if i.val < 872 then
(if i.val < 870 then
(if i.val < 869 then
128
else
525)
else
(if i.val < 871 then
160
else
159))
else
(if i.val < 874 then
(if i.val < 873 then
516
else
526)
else
(if i.val < 875 then
178
else
(if i.val < 876 then
495
else
497)))))))
else
(if i.val < 911 then
(if i.val < 894 then
(if i.val < 885 then
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
527
else
528)
else
(if i.val < 880 then
502
else
164))
else
(if i.val < 883 then
(if i.val < 882 then
234
else
231)
else
(if i.val < 884 then
529
else
524)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
529
else
217)
else
(if i.val < 888 then
530
else
523))
else
(if i.val < 891 then
(if i.val < 890 then
530
else
531)
else
(if i.val < 892 then
517
else
(if i.val < 893 then
166
else
140)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
137
else
500)
else
(if i.val < 897 then
532
else
155))
else
(if i.val < 900 then
(if i.val < 899 then
532
else
533)
else
(if i.val < 901 then
534
else
215)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
188
else
240)
else
(if i.val < 905 then
189
else
225))
else
(if i.val < 908 then
(if i.val < 907 then
514
else
11)
else
(if i.val < 909 then
506
else
(if i.val < 910 then
522
else
535))))))
else
(if i.val < 928 then
(if i.val < 919 then
(if i.val < 915 then
(if i.val < 913 then
(if i.val < 912 then
534
else
149)
else
(if i.val < 914 then
165
else
136))
else
(if i.val < 917 then
(if i.val < 916 then
204
else
185)
else
(if i.val < 918 then
505
else
513)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
181
else
126)
else
(if i.val < 922 then
536
else
124))
else
(if i.val < 925 then
(if i.val < 924 then
537
else
129)
else
(if i.val < 926 then
184
else
(if i.val < 927 then
525
else
498)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
224
else
536)
else
(if i.val < 931 then
509
else
519))
else
(if i.val < 934 then
(if i.val < 933 then
492
else
232)
else
(if i.val < 935 then
538
else
227)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
496
else
230)
else
(if i.val < 939 then
538
else
209))
else
(if i.val < 942 then
(if i.val < 941 then
533
else
520)
else
(if i.val < 943 then
5
else
(if i.val < 944 then
507
else
153))))))))
else
(if i.val < 1012 then
(if i.val < 978 then
(if i.val < 961 then
(if i.val < 953 then
(if i.val < 949 then
(if i.val < 947 then
(if i.val < 946 then
186
else
134)
else
(if i.val < 948 then
207
else
169))
else
(if i.val < 951 then
(if i.val < 950 then
537
else
499)
else
(if i.val < 952 then
198
else
535)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
491
else
521)
else
(if i.val < 956 then
201
else
539))
else
(if i.val < 959 then
(if i.val < 958 then
526
else
503)
else
(if i.val < 960 then
190
else
539))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
504
else
17)
else
(if i.val < 964 then
518
else
158))
else
(if i.val < 967 then
(if i.val < 966 then
200
else
531)
else
(if i.val < 968 then
228
else
173)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
182
else
510)
else
(if i.val < 972 then
176
else
540))
else
(if i.val < 975 then
(if i.val < 974 then
174
else
210)
else
(if i.val < 976 then
540
else
(if i.val < 977 then
541
else
501))))))
else
(if i.val < 995 then
(if i.val < 986 then
(if i.val < 982 then
(if i.val < 980 then
(if i.val < 979 then
528
else
229)
else
(if i.val < 981 then
205
else
168))
else
(if i.val < 984 then
(if i.val < 983 then
235
else
13)
else
(if i.val < 985 then
256
else
30)))
else
(if i.val < 990 then
(if i.val < 988 then
(if i.val < 987 then
323
else
542)
else
(if i.val < 989 then
301
else
543))
else
(if i.val < 992 then
(if i.val < 991 then
369
else
544)
else
(if i.val < 993 then
339
else
(if i.val < 994 then
280
else
356)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
324
else
545)
else
(if i.val < 998 then
372
else
546))
else
(if i.val < 1001 then
(if i.val < 1000 then
547
else
299)
else
(if i.val < 1002 then
274
else
548)))
else
(if i.val < 1007 then
(if i.val < 1005 then
(if i.val < 1004 then
285
else
343)
else
(if i.val < 1006 then
336
else
351))
else
(if i.val < 1009 then
(if i.val < 1008 then
342
else
549)
else
(if i.val < 1010 then
375
else
(if i.val < 1011 then
35
else
543)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
545
else
306)
else
(if i.val < 1015 then
544
else
378))
else
(if i.val < 1018 then
(if i.val < 1017 then
307
else
311)
else
(if i.val < 1019 then
310
else
320)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
377
else
282)
else
(if i.val < 1023 then
31
else
327))
else
(if i.val < 1026 then
(if i.val < 1025 then
329
else
315)
else
(if i.val < 1027 then
365
else
(if i.val < 1028 then
550
else
32)))))
else
(if i.val < 1037 then
(if i.val < 1033 then
(if i.val < 1031 then
(if i.val < 1030 then
551
else
321)
else
(if i.val < 1032 then
373
else
262))
else
(if i.val < 1035 then
(if i.val < 1034 then
340
else
318)
else
(if i.val < 1036 then
313
else
367)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
346
else
380)
else
(if i.val < 1040 then
379
else
304))
else
(if i.val < 1043 then
(if i.val < 1042 then
309
else
551)
else
(if i.val < 1044 then
549
else
(if i.val < 1045 then
550
else
376))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
248
else
312)
else
(if i.val < 1049 then
546
else
334))
else
(if i.val < 1052 then
(if i.val < 1051 then
266
else
297)
else
(if i.val < 1053 then
36
else
263)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
37
else
265)
else
(if i.val < 1057 then
547
else
542))
else
(if i.val < 1060 then
(if i.val < 1059 then
374
else
344)
else
(if i.val < 1061 then
246
else
(if i.val < 1062 then
293
else
45)))))
else
(if i.val < 1071 then
(if i.val < 1067 then
(if i.val < 1065 then
(if i.val < 1064 then
27
else
371)
else
(if i.val < 1066 then
463
else
471))
else
(if i.val < 1069 then
(if i.val < 1068 then
384
else
456)
else
(if i.val < 1070 then
432
else
490)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
484
else
457)
else
(if i.val < 1074 then
107
else
119))
else
(if i.val < 1077 then
(if i.val < 1076 then
466
else
77)
else
(if i.val < 1078 then
420
else
(if i.val < 1079 then
387
else
468)))))))))))

def g32p_row06_cosetDistances2 : Fin 1080 → ℕ :=
  fun i => (if i.val < 540 then
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
(if i.val < 32 then
0
else
0))))))
else
(if i.val < 50 then
(if i.val < 41 then
(if i.val < 37 then
(if i.val < 35 then
(if i.val < 34 then
0
else
0)
else
(if i.val < 36 then
0
else
0))
else
(if i.val < 39 then
(if i.val < 38 then
0
else
0)
else
(if i.val < 40 then
0
else
0)))
else
(if i.val < 45 then
(if i.val < 43 then
(if i.val < 42 then
0
else
0)
else
(if i.val < 44 then
0
else
0))
else
(if i.val < 47 then
(if i.val < 46 then
0
else
0)
else
(if i.val < 48 then
0
else
(if i.val < 49 then
0
else
0)))))
else
(if i.val < 58 then
(if i.val < 54 then
(if i.val < 52 then
(if i.val < 51 then
0
else
0)
else
(if i.val < 53 then
0
else
0))
else
(if i.val < 56 then
(if i.val < 55 then
1
else
0)
else
(if i.val < 57 then
0
else
0)))
else
(if i.val < 62 then
(if i.val < 60 then
(if i.val < 59 then
0
else
0)
else
(if i.val < 61 then
0
else
1))
else
(if i.val < 64 then
(if i.val < 63 then
0
else
0)
else
(if i.val < 65 then
0
else
(if i.val < 66 then
0
else
0)))))))
else
(if i.val < 101 then
(if i.val < 84 then
(if i.val < 75 then
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
0
else
0)
else
(if i.val < 70 then
0
else
0))
else
(if i.val < 73 then
(if i.val < 72 then
0
else
0)
else
(if i.val < 74 then
0
else
0)))
else
(if i.val < 79 then
(if i.val < 77 then
(if i.val < 76 then
0
else
0)
else
(if i.val < 78 then
0
else
0))
else
(if i.val < 81 then
(if i.val < 80 then
0
else
0)
else
(if i.val < 82 then
0
else
(if i.val < 83 then
0
else
0)))))
else
(if i.val < 92 then
(if i.val < 88 then
(if i.val < 86 then
(if i.val < 85 then
1
else
0)
else
(if i.val < 87 then
0
else
0))
else
(if i.val < 90 then
(if i.val < 89 then
0
else
0)
else
(if i.val < 91 then
0
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
0
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
0
else
(if i.val < 100 then
1
else
0))))))
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
0))
else
(if i.val < 107 then
(if i.val < 106 then
0
else
0)
else
(if i.val < 108 then
0
else
1)))
else
(if i.val < 113 then
(if i.val < 111 then
(if i.val < 110 then
1
else
0)
else
(if i.val < 112 then
0
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
0
else
(if i.val < 117 then
0
else
1)))))
else
(if i.val < 126 then
(if i.val < 122 then
(if i.val < 120 then
(if i.val < 119 then
0
else
0)
else
(if i.val < 121 then
0
else
0))
else
(if i.val < 124 then
(if i.val < 123 then
0
else
0)
else
(if i.val < 125 then
0
else
1)))
else
(if i.val < 130 then
(if i.val < 128 then
(if i.val < 127 then
1
else
0)
else
(if i.val < 129 then
0
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
0
else
(if i.val < 134 then
0
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
0
else
0)
else
(if i.val < 138 then
0
else
0))
else
(if i.val < 141 then
(if i.val < 140 then
0
else
0)
else
(if i.val < 142 then
0
else
0)))
else
(if i.val < 147 then
(if i.val < 145 then
(if i.val < 144 then
0
else
0)
else
(if i.val < 146 then
0
else
0))
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
0))))
else
(if i.val < 159 then
(if i.val < 155 then
(if i.val < 153 then
(if i.val < 152 then
0
else
0)
else
(if i.val < 154 then
0
else
1))
else
(if i.val < 157 then
(if i.val < 156 then
0
else
0)
else
(if i.val < 158 then
0
else
0)))
else
(if i.val < 163 then
(if i.val < 161 then
(if i.val < 160 then
1
else
0)
else
(if i.val < 162 then
0
else
0))
else
(if i.val < 165 then
(if i.val < 164 then
0
else
0)
else
(if i.val < 166 then
0
else
(if i.val < 167 then
0
else
0))))))
else
(if i.val < 185 then
(if i.val < 176 then
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
1))
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
0)))
else
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
(if i.val < 184 then
0
else
0)))))
else
(if i.val < 193 then
(if i.val < 189 then
(if i.val < 187 then
(if i.val < 186 then
0
else
1)
else
(if i.val < 188 then
0
else
0))
else
(if i.val < 191 then
(if i.val < 190 then
0
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
0
else
0)
else
(if i.val < 196 then
0
else
0))
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
0
else
0)))))))
else
(if i.val < 236 then
(if i.val < 219 then
(if i.val < 210 then
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
0
else
0)
else
(if i.val < 205 then
0
else
0))
else
(if i.val < 208 then
(if i.val < 207 then
0
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
0
else
0)
else
(if i.val < 213 then
0
else
0))
else
(if i.val < 216 then
(if i.val < 215 then
0
else
0)
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
0
else
0)
else
(if i.val < 222 then
0
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
0
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
0
else
0))
else
(if i.val < 233 then
(if i.val < 232 then
0
else
0)
else
(if i.val < 234 then
0
else
(if i.val < 235 then
0
else
1))))))
else
(if i.val < 253 then
(if i.val < 244 then
(if i.val < 240 then
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
1))
else
(if i.val < 242 then
(if i.val < 241 then
0
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
0)
else
(if i.val < 251 then
0
else
(if i.val < 252 then
0
else
0)))))
else
(if i.val < 261 then
(if i.val < 257 then
(if i.val < 255 then
(if i.val < 254 then
1
else
1)
else
(if i.val < 256 then
0
else
0))
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
0)))
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
1))
else
(if i.val < 267 then
(if i.val < 266 then
0
else
1)
else
(if i.val < 268 then
1
else
(if i.val < 269 then
1
else
0)))))))))
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
0)
else
(if i.val < 273 then
0
else
1))
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
1)))
else
(if i.val < 282 then
(if i.val < 280 then
(if i.val < 279 then
0
else
0)
else
(if i.val < 281 then
1
else
0))
else
(if i.val < 284 then
(if i.val < 283 then
0
else
1)
else
(if i.val < 285 then
0
else
1))))
else
(if i.val < 294 then
(if i.val < 290 then
(if i.val < 288 then
(if i.val < 287 then
0
else
0)
else
(if i.val < 289 then
1
else
1))
else
(if i.val < 292 then
(if i.val < 291 then
1
else
1)
else
(if i.val < 293 then
1
else
0)))
else
(if i.val < 298 then
(if i.val < 296 then
(if i.val < 295 then
0
else
0)
else
(if i.val < 297 then
0
else
0))
else
(if i.val < 300 then
(if i.val < 299 then
0
else
0)
else
(if i.val < 301 then
0
else
(if i.val < 302 then
0
else
0))))))
else
(if i.val < 320 then
(if i.val < 311 then
(if i.val < 307 then
(if i.val < 305 then
(if i.val < 304 then
0
else
1)
else
(if i.val < 306 then
0
else
0))
else
(if i.val < 309 then
(if i.val < 308 then
0
else
0)
else
(if i.val < 310 then
0
else
1)))
else
(if i.val < 315 then
(if i.val < 313 then
(if i.val < 312 then
0
else
0)
else
(if i.val < 314 then
0
else
0))
else
(if i.val < 317 then
(if i.val < 316 then
0
else
0)
else
(if i.val < 318 then
0
else
(if i.val < 319 then
0
else
0)))))
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
1
else
(if i.val < 336 then
0
else
0)))))))
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
0
else
0))
else
(if i.val < 343 then
(if i.val < 342 then
0
else
0)
else
(if i.val < 344 then
0
else
0)))
else
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
0
else
0)
else
(if i.val < 348 then
1
else
0))
else
(if i.val < 351 then
(if i.val < 350 then
0
else
1)
else
(if i.val < 352 then
0
else
(if i.val < 353 then
0
else
0)))))
else
(if i.val < 362 then
(if i.val < 358 then
(if i.val < 356 then
(if i.val < 355 then
0
else
0)
else
(if i.val < 357 then
1
else
0))
else
(if i.val < 360 then
(if i.val < 359 then
0
else
0)
else
(if i.val < 361 then
0
else
0)))
else
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
0
else
0)
else
(if i.val < 365 then
0
else
0))
else
(if i.val < 368 then
(if i.val < 367 then
0
else
1)
else
(if i.val < 369 then
1
else
(if i.val < 370 then
0
else
0))))))
else
(if i.val < 388 then
(if i.val < 379 then
(if i.val < 375 then
(if i.val < 373 then
(if i.val < 372 then
0
else
0)
else
(if i.val < 374 then
0
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
0)))
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
0))
else
(if i.val < 385 then
(if i.val < 384 then
1
else
0)
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
0)))
else
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
0
else
0)
else
(if i.val < 399 then
0
else
0))
else
(if i.val < 402 then
(if i.val < 401 then
0
else
0)
else
(if i.val < 403 then
1
else
(if i.val < 404 then
0
else
0))))))))
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
0)
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
0)))
else
(if i.val < 417 then
(if i.val < 415 then
(if i.val < 414 then
1
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
0
else
0)
else
(if i.val < 420 then
0
else
0))))
else
(if i.val < 429 then
(if i.val < 425 then
(if i.val < 423 then
(if i.val < 422 then
1
else
1)
else
(if i.val < 424 then
1
else
1))
else
(if i.val < 427 then
(if i.val < 426 then
1
else
0)
else
(if i.val < 428 then
0
else
1)))
else
(if i.val < 433 then
(if i.val < 431 then
(if i.val < 430 then
1
else
0)
else
(if i.val < 432 then
0
else
1))
else
(if i.val < 435 then
(if i.val < 434 then
1
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
0)
else
(if i.val < 441 then
1
else
1))
else
(if i.val < 444 then
(if i.val < 443 then
1
else
1)
else
(if i.val < 445 then
1
else
1)))
else
(if i.val < 450 then
(if i.val < 448 then
(if i.val < 447 then
0
else
1)
else
(if i.val < 449 then
1
else
1))
else
(if i.val < 452 then
(if i.val < 451 then
1
else
1)
else
(if i.val < 453 then
1
else
(if i.val < 454 then
0
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
1
else
1)))
else
(if i.val < 467 then
(if i.val < 465 then
(if i.val < 464 then
0
else
0)
else
(if i.val < 466 then
0
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
0
else
(if i.val < 471 then
1
else
0)))))))
else
(if i.val < 506 then
(if i.val < 489 then
(if i.val < 480 then
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
1
else
1)
else
(if i.val < 475 then
1
else
0))
else
(if i.val < 478 then
(if i.val < 477 then
1
else
1)
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
1
else
1)))))
else
(if i.val < 497 then
(if i.val < 493 then
(if i.val < 491 then
(if i.val < 490 then
1
else
1)
else
(if i.val < 492 then
1
else
1))
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
1)))
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
1
else
1)
else
(if i.val < 504 then
1
else
(if i.val < 505 then
1
else
1))))))
else
(if i.val < 523 then
(if i.val < 514 then
(if i.val < 510 then
(if i.val < 508 then
(if i.val < 507 then
0
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
1
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
1
else
1)
else
(if i.val < 517 then
1
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
0
else
(if i.val < 522 then
1
else
0)))))
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
1
else
1))
else
(if i.val < 529 then
(if i.val < 528 then
1
else
1)
else
(if i.val < 530 then
0
else
1)))
else
(if i.val < 535 then
(if i.val < 533 then
(if i.val < 532 then
1
else
0)
else
(if i.val < 534 then
0
else
1))
else
(if i.val < 537 then
(if i.val < 536 then
1
else
0)
else
(if i.val < 538 then
0
else
(if i.val < 539 then
0
else
0))))))))))
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
0)
else
(if i.val < 543 then
0
else
0))
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
0
else
0)
else
(if i.val < 551 then
0
else
0))
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
0))))
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
0))
else
(if i.val < 562 then
(if i.val < 561 then
1
else
0)
else
(if i.val < 563 then
0
else
0)))
else
(if i.val < 568 then
(if i.val < 566 then
(if i.val < 565 then
0
else
0)
else
(if i.val < 567 then
1
else
1))
else
(if i.val < 570 then
(if i.val < 569 then
0
else
1)
else
(if i.val < 571 then
0
else
(if i.val < 572 then
1
else
0))))))
else
(if i.val < 590 then
(if i.val < 581 then
(if i.val < 577 then
(if i.val < 575 then
(if i.val < 574 then
1
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
0)
else
(if i.val < 580 then
0
else
0)))
else
(if i.val < 585 then
(if i.val < 583 then
(if i.val < 582 then
0
else
0)
else
(if i.val < 584 then
0
else
0))
else
(if i.val < 587 then
(if i.val < 586 then
0
else
0)
else
(if i.val < 588 then
0
else
(if i.val < 589 then
0
else
0)))))
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
0
else
0))
else
(if i.val < 596 then
(if i.val < 595 then
0
else
0)
else
(if i.val < 597 then
1
else
0)))
else
(if i.val < 602 then
(if i.val < 600 then
(if i.val < 599 then
0
else
0)
else
(if i.val < 601 then
0
else
0))
else
(if i.val < 604 then
(if i.val < 603 then
1
else
0)
else
(if i.val < 605 then
0
else
(if i.val < 606 then
0
else
1)))))))
else
(if i.val < 641 then
(if i.val < 624 then
(if i.val < 615 then
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
1
else
1)
else
(if i.val < 610 then
0
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
0)))
else
(if i.val < 619 then
(if i.val < 617 then
(if i.val < 616 then
0
else
0)
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
1
else
1)))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
0
else
1)
else
(if i.val < 627 then
1
else
1))
else
(if i.val < 630 then
(if i.val < 629 then
0
else
1)
else
(if i.val < 631 then
0
else
1)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
1
else
0)
else
(if i.val < 635 then
1
else
1))
else
(if i.val < 638 then
(if i.val < 637 then
1
else
0)
else
(if i.val < 639 then
0
else
(if i.val < 640 then
1
else
1))))))
else
(if i.val < 658 then
(if i.val < 649 then
(if i.val < 645 then
(if i.val < 643 then
(if i.val < 642 then
0
else
1)
else
(if i.val < 644 then
0
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
1)))
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
1)
else
(if i.val < 656 then
0
else
(if i.val < 657 then
0
else
0)))))
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
1
else
0))
else
(if i.val < 664 then
(if i.val < 663 then
0
else
1)
else
(if i.val < 665 then
0
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
0
else
0)
else
(if i.val < 673 then
1
else
(if i.val < 674 then
1
else
1))))))))
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
0
else
1))
else
(if i.val < 681 then
(if i.val < 680 then
1
else
1)
else
(if i.val < 682 then
1
else
0)))
else
(if i.val < 687 then
(if i.val < 685 then
(if i.val < 684 then
0
else
0)
else
(if i.val < 686 then
0
else
0))
else
(if i.val < 689 then
(if i.val < 688 then
1
else
1)
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
1))
else
(if i.val < 697 then
(if i.val < 696 then
1
else
1)
else
(if i.val < 698 then
1
else
0)))
else
(if i.val < 703 then
(if i.val < 701 then
(if i.val < 700 then
1
else
1)
else
(if i.val < 702 then
1
else
1))
else
(if i.val < 705 then
(if i.val < 704 then
1
else
1)
else
(if i.val < 706 then
1
else
(if i.val < 707 then
1
else
0))))))
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
1
else
1)
else
(if i.val < 715 then
1
else
1)))
else
(if i.val < 720 then
(if i.val < 718 then
(if i.val < 717 then
1
else
1)
else
(if i.val < 719 then
1
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
1)))))
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
1
else
1))
else
(if i.val < 731 then
(if i.val < 730 then
1
else
0)
else
(if i.val < 732 then
1
else
0)))
else
(if i.val < 737 then
(if i.val < 735 then
(if i.val < 734 then
1
else
1)
else
(if i.val < 736 then
1
else
1))
else
(if i.val < 739 then
(if i.val < 738 then
1
else
1)
else
(if i.val < 740 then
0
else
(if i.val < 741 then
1
else
1)))))))
else
(if i.val < 776 then
(if i.val < 759 then
(if i.val < 750 then
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
1
else
1)
else
(if i.val < 745 then
1
else
1))
else
(if i.val < 748 then
(if i.val < 747 then
1
else
1)
else
(if i.val < 749 then
1
else
1)))
else
(if i.val < 754 then
(if i.val < 752 then
(if i.val < 751 then
1
else
1)
else
(if i.val < 753 then
1
else
1))
else
(if i.val < 756 then
(if i.val < 755 then
1
else
0)
else
(if i.val < 757 then
1
else
(if i.val < 758 then
0
else
0)))))
else
(if i.val < 767 then
(if i.val < 763 then
(if i.val < 761 then
(if i.val < 760 then
1
else
1)
else
(if i.val < 762 then
1
else
0))
else
(if i.val < 765 then
(if i.val < 764 then
1
else
1)
else
(if i.val < 766 then
1
else
1)))
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
1
else
1)
else
(if i.val < 774 then
1
else
(if i.val < 775 then
1
else
1))))))
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
1
else
1))
else
(if i.val < 782 then
(if i.val < 781 then
1
else
0)
else
(if i.val < 783 then
0
else
1)))
else
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1
else
1)
else
(if i.val < 787 then
1
else
1))
else
(if i.val < 790 then
(if i.val < 789 then
1
else
1)
else
(if i.val < 791 then
1
else
(if i.val < 792 then
1
else
1)))))
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
1
else
0)))
else
(if i.val < 805 then
(if i.val < 803 then
(if i.val < 802 then
0
else
0)
else
(if i.val < 804 then
0
else
1))
else
(if i.val < 807 then
(if i.val < 806 then
0
else
0)
else
(if i.val < 808 then
0
else
(if i.val < 809 then
0
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
0
else
0))
else
(if i.val < 816 then
(if i.val < 815 then
0
else
1)
else
(if i.val < 817 then
1
else
0)))
else
(if i.val < 822 then
(if i.val < 820 then
(if i.val < 819 then
1
else
0)
else
(if i.val < 821 then
0
else
0))
else
(if i.val < 824 then
(if i.val < 823 then
1
else
0)
else
(if i.val < 825 then
0
else
1))))
else
(if i.val < 834 then
(if i.val < 830 then
(if i.val < 828 then
(if i.val < 827 then
1
else
1)
else
(if i.val < 829 then
0
else
0))
else
(if i.val < 832 then
(if i.val < 831 then
0
else
0)
else
(if i.val < 833 then
0
else
1)))
else
(if i.val < 838 then
(if i.val < 836 then
(if i.val < 835 then
0
else
1)
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
1)
else
(if i.val < 841 then
1
else
(if i.val < 842 then
1
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
1
else
1))
else
(if i.val < 849 then
(if i.val < 848 then
1
else
1)
else
(if i.val < 850 then
1
else
1)))
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
1))
else
(if i.val < 857 then
(if i.val < 856 then
0
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
1
else
0)
else
(if i.val < 863 then
0
else
1))
else
(if i.val < 866 then
(if i.val < 865 then
1
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
1))
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
1
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
0)
else
(if i.val < 880 then
1
else
1))
else
(if i.val < 883 then
(if i.val < 882 then
1
else
1)
else
(if i.val < 884 then
0
else
1)))
else
(if i.val < 889 then
(if i.val < 887 then
(if i.val < 886 then
1
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
1
else
1)))))
else
(if i.val < 902 then
(if i.val < 898 then
(if i.val < 896 then
(if i.val < 895 then
1
else
1)
else
(if i.val < 897 then
0
else
1))
else
(if i.val < 900 then
(if i.val < 899 then
1
else
0)
else
(if i.val < 901 then
0
else
1)))
else
(if i.val < 906 then
(if i.val < 904 then
(if i.val < 903 then
1
else
1)
else
(if i.val < 905 then
1
else
1))
else
(if i.val < 908 then
(if i.val < 907 then
1
else
1)
else
(if i.val < 909 then
1
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
1)
else
(if i.val < 914 then
1
else
1))
else
(if i.val < 917 then
(if i.val < 916 then
1
else
1)
else
(if i.val < 918 then
1
else
1)))
else
(if i.val < 923 then
(if i.val < 921 then
(if i.val < 920 then
1
else
1)
else
(if i.val < 922 then
0
else
1))
else
(if i.val < 925 then
(if i.val < 924 then
0
else
1)
else
(if i.val < 926 then
1
else
(if i.val < 927 then
1
else
1)))))
else
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
1
else
1)
else
(if i.val < 931 then
1
else
1))
else
(if i.val < 934 then
(if i.val < 933 then
1
else
1)
else
(if i.val < 935 then
0
else
1)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
1
else
1)
else
(if i.val < 939 then
1
else
1))
else
(if i.val < 942 then
(if i.val < 941 then
1
else
1)
else
(if i.val < 943 then
1
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
1)
else
(if i.val < 948 then
1
else
1))
else
(if i.val < 951 then
(if i.val < 950 then
1
else
1)
else
(if i.val < 952 then
1
else
1)))
else
(if i.val < 957 then
(if i.val < 955 then
(if i.val < 954 then
1
else
1)
else
(if i.val < 956 then
1
else
0))
else
(if i.val < 959 then
(if i.val < 958 then
1
else
1)
else
(if i.val < 960 then
1
else
1))))
else
(if i.val < 969 then
(if i.val < 965 then
(if i.val < 963 then
(if i.val < 962 then
1
else
1)
else
(if i.val < 964 then
1
else
1))
else
(if i.val < 967 then
(if i.val < 966 then
1
else
1)
else
(if i.val < 968 then
1
else
1)))
else
(if i.val < 973 then
(if i.val < 971 then
(if i.val < 970 then
1
else
1)
else
(if i.val < 972 then
1
else
0))
else
(if i.val < 975 then
(if i.val < 974 then
1
else
1)
else
(if i.val < 976 then
1
else
(if i.val < 977 then
0
else
1))))))
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
1
else
1))
else
(if i.val < 984 then
(if i.val < 983 then
1
else
1)
else
(if i.val < 985 then
1
else
1)))
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
1
else
1)))))
else
(if i.val < 1003 then
(if i.val < 999 then
(if i.val < 997 then
(if i.val < 996 then
1
else
0)
else
(if i.val < 998 then
1
else
0))
else
(if i.val < 1001 then
(if i.val < 1000 then
0
else
1)
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
1))
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
1
else
1)))))))
else
(if i.val < 1046 then
(if i.val < 1029 then
(if i.val < 1020 then
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
1
else
1)
else
(if i.val < 1015 then
1
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
1
else
1)))
else
(if i.val < 1024 then
(if i.val < 1022 then
(if i.val < 1021 then
1
else
1)
else
(if i.val < 1023 then
1
else
1))
else
(if i.val < 1026 then
(if i.val < 1025 then
1
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
0
else
1)
else
(if i.val < 1032 then
1
else
1))
else
(if i.val < 1035 then
(if i.val < 1034 then
1
else
1)
else
(if i.val < 1036 then
1
else
1)))
else
(if i.val < 1041 then
(if i.val < 1039 then
(if i.val < 1038 then
1
else
1)
else
(if i.val < 1040 then
1
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
1
else
(if i.val < 1045 then
1
else
1))))))
else
(if i.val < 1063 then
(if i.val < 1054 then
(if i.val < 1050 then
(if i.val < 1048 then
(if i.val < 1047 then
1
else
1)
else
(if i.val < 1049 then
1
else
1))
else
(if i.val < 1052 then
(if i.val < 1051 then
1
else
1)
else
(if i.val < 1053 then
1
else
1)))
else
(if i.val < 1058 then
(if i.val < 1056 then
(if i.val < 1055 then
1
else
1)
else
(if i.val < 1057 then
1
else
1))
else
(if i.val < 1060 then
(if i.val < 1059 then
1
else
1)
else
(if i.val < 1061 then
1
else
(if i.val < 1062 then
1
else
1)))))
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
1
else
1))
else
(if i.val < 1069 then
(if i.val < 1068 then
1
else
1)
else
(if i.val < 1070 then
1
else
1)))
else
(if i.val < 1075 then
(if i.val < 1073 then
(if i.val < 1072 then
1
else
1)
else
(if i.val < 1074 then
1
else
1))
else
(if i.val < 1077 then
(if i.val < 1076 then
1
else
1)
else
(if i.val < 1078 then
1
else
(if i.val < 1079 then
1
else
1)))))))))))

def g32p_row06_cosetRoots2 : Fin 552 → Fin 1080 :=
  fun i => (if i.val < 276 then
(if i.val < 138 then
(if i.val < 69 then
(if i.val < 34 then
(if i.val < 17 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
0
else
1)
else
(if i.val < 3 then
2
else
3))
else
(if i.val < 6 then
(if i.val < 5 then
4
else
5)
else
(if i.val < 7 then
6
else
7)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
8
else
9)
else
(if i.val < 11 then
10
else
11))
else
(if i.val < 14 then
(if i.val < 13 then
12
else
13)
else
(if i.val < 15 then
14
else
(if i.val < 16 then
15
else
16)))))
else
(if i.val < 25 then
(if i.val < 21 then
(if i.val < 19 then
(if i.val < 18 then
17
else
18)
else
(if i.val < 20 then
19
else
20))
else
(if i.val < 23 then
(if i.val < 22 then
21
else
22)
else
(if i.val < 24 then
23
else
24)))
else
(if i.val < 29 then
(if i.val < 27 then
(if i.val < 26 then
25
else
26)
else
(if i.val < 28 then
27
else
28))
else
(if i.val < 31 then
(if i.val < 30 then
29
else
30)
else
(if i.val < 32 then
31
else
(if i.val < 33 then
32
else
33))))))
else
(if i.val < 51 then
(if i.val < 42 then
(if i.val < 38 then
(if i.val < 36 then
(if i.val < 35 then
34
else
35)
else
(if i.val < 37 then
36
else
37))
else
(if i.val < 40 then
(if i.val < 39 then
38
else
39)
else
(if i.val < 41 then
40
else
41)))
else
(if i.val < 46 then
(if i.val < 44 then
(if i.val < 43 then
42
else
43)
else
(if i.val < 45 then
44
else
45))
else
(if i.val < 48 then
(if i.val < 47 then
46
else
47)
else
(if i.val < 49 then
48
else
(if i.val < 50 then
49
else
50)))))
else
(if i.val < 60 then
(if i.val < 55 then
(if i.val < 53 then
(if i.val < 52 then
51
else
52)
else
(if i.val < 54 then
53
else
55))
else
(if i.val < 57 then
(if i.val < 56 then
56
else
57)
else
(if i.val < 58 then
58
else
(if i.val < 59 then
59
else
60))))
else
(if i.val < 64 then
(if i.val < 62 then
(if i.val < 61 then
62
else
63)
else
(if i.val < 63 then
64
else
65))
else
(if i.val < 66 then
(if i.val < 65 then
66
else
67)
else
(if i.val < 67 then
68
else
(if i.val < 68 then
69
else
70)))))))
else
(if i.val < 103 then
(if i.val < 86 then
(if i.val < 77 then
(if i.val < 73 then
(if i.val < 71 then
(if i.val < 70 then
71
else
72)
else
(if i.val < 72 then
73
else
74))
else
(if i.val < 75 then
(if i.val < 74 then
75
else
76)
else
(if i.val < 76 then
77
else
78)))
else
(if i.val < 81 then
(if i.val < 79 then
(if i.val < 78 then
79
else
80)
else
(if i.val < 80 then
81
else
82))
else
(if i.val < 83 then
(if i.val < 82 then
83
else
85)
else
(if i.val < 84 then
86
else
(if i.val < 85 then
87
else
88)))))
else
(if i.val < 94 then
(if i.val < 90 then
(if i.val < 88 then
(if i.val < 87 then
89
else
90)
else
(if i.val < 89 then
91
else
93))
else
(if i.val < 92 then
(if i.val < 91 then
94
else
95)
else
(if i.val < 93 then
97
else
98)))
else
(if i.val < 98 then
(if i.val < 96 then
(if i.val < 95 then
100
else
101)
else
(if i.val < 97 then
103
else
104))
else
(if i.val < 100 then
(if i.val < 99 then
105
else
106)
else
(if i.val < 101 then
107
else
(if i.val < 102 then
110
else
111))))))
else
(if i.val < 120 then
(if i.val < 111 then
(if i.val < 107 then
(if i.val < 105 then
(if i.val < 104 then
112
else
114)
else
(if i.val < 106 then
115
else
116))
else
(if i.val < 109 then
(if i.val < 108 then
118
else
119)
else
(if i.val < 110 then
120
else
121)))
else
(if i.val < 115 then
(if i.val < 113 then
(if i.val < 112 then
122
else
123)
else
(if i.val < 114 then
124
else
127))
else
(if i.val < 117 then
(if i.val < 116 then
128
else
129)
else
(if i.val < 118 then
131
else
(if i.val < 119 then
132
else
133)))))
else
(if i.val < 129 then
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
134
else
135)
else
(if i.val < 123 then
136
else
137))
else
(if i.val < 126 then
(if i.val < 125 then
138
else
139)
else
(if i.val < 127 then
140
else
(if i.val < 128 then
141
else
142))))
else
(if i.val < 133 then
(if i.val < 131 then
(if i.val < 130 then
143
else
144)
else
(if i.val < 132 then
145
else
146))
else
(if i.val < 135 then
(if i.val < 134 then
147
else
149)
else
(if i.val < 136 then
150
else
(if i.val < 137 then
151
else
152))))))))
else
(if i.val < 207 then
(if i.val < 172 then
(if i.val < 155 then
(if i.val < 146 then
(if i.val < 142 then
(if i.val < 140 then
(if i.val < 139 then
153
else
155)
else
(if i.val < 141 then
156
else
157))
else
(if i.val < 144 then
(if i.val < 143 then
158
else
160)
else
(if i.val < 145 then
161
else
162)))
else
(if i.val < 150 then
(if i.val < 148 then
(if i.val < 147 then
163
else
164)
else
(if i.val < 149 then
165
else
166))
else
(if i.val < 152 then
(if i.val < 151 then
167
else
168)
else
(if i.val < 153 then
169
else
(if i.val < 154 then
170
else
172)))))
else
(if i.val < 163 then
(if i.val < 159 then
(if i.val < 157 then
(if i.val < 156 then
173
else
174)
else
(if i.val < 158 then
175
else
176))
else
(if i.val < 161 then
(if i.val < 160 then
177
else
178)
else
(if i.val < 162 then
179
else
180)))
else
(if i.val < 167 then
(if i.val < 165 then
(if i.val < 164 then
181
else
182)
else
(if i.val < 166 then
183
else
184))
else
(if i.val < 169 then
(if i.val < 168 then
185
else
187)
else
(if i.val < 170 then
188
else
(if i.val < 171 then
189
else
190))))))
else
(if i.val < 189 then
(if i.val < 180 then
(if i.val < 176 then
(if i.val < 174 then
(if i.val < 173 then
192
else
193)
else
(if i.val < 175 then
194
else
195))
else
(if i.val < 178 then
(if i.val < 177 then
196
else
197)
else
(if i.val < 179 then
199
else
200)))
else
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
201
else
202)
else
(if i.val < 183 then
203
else
204))
else
(if i.val < 186 then
(if i.val < 185 then
205
else
206)
else
(if i.val < 187 then
207
else
(if i.val < 188 then
209
else
210)))))
else
(if i.val < 198 then
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
211
else
212)
else
(if i.val < 192 then
213
else
214))
else
(if i.val < 195 then
(if i.val < 194 then
215
else
216)
else
(if i.val < 196 then
219
else
(if i.val < 197 then
220
else
221))))
else
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
222
else
224)
else
(if i.val < 201 then
225
else
226))
else
(if i.val < 204 then
(if i.val < 203 then
228
else
229)
else
(if i.val < 205 then
230
else
(if i.val < 206 then
231
else
232)))))))
else
(if i.val < 241 then
(if i.val < 224 then
(if i.val < 215 then
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
233
else
234)
else
(if i.val < 210 then
236
else
237))
else
(if i.val < 213 then
(if i.val < 212 then
238
else
240)
else
(if i.val < 214 then
241
else
243)))
else
(if i.val < 219 then
(if i.val < 217 then
(if i.val < 216 then
245
else
248)
else
(if i.val < 218 then
249
else
250))
else
(if i.val < 221 then
(if i.val < 220 then
251
else
252)
else
(if i.val < 222 then
255
else
(if i.val < 223 then
256
else
257)))))
else
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
259
else
260)
else
(if i.val < 227 then
262
else
265))
else
(if i.val < 230 then
(if i.val < 229 then
269
else
270)
else
(if i.val < 231 then
271
else
272)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
274
else
275)
else
(if i.val < 235 then
278
else
279))
else
(if i.val < 238 then
(if i.val < 237 then
281
else
282)
else
(if i.val < 239 then
284
else
(if i.val < 240 then
286
else
287))))))
else
(if i.val < 258 then
(if i.val < 249 then
(if i.val < 245 then
(if i.val < 243 then
(if i.val < 242 then
293
else
294)
else
(if i.val < 244 then
295
else
296))
else
(if i.val < 247 then
(if i.val < 246 then
297
else
298)
else
(if i.val < 248 then
299
else
300)))
else
(if i.val < 253 then
(if i.val < 251 then
(if i.val < 250 then
301
else
302)
else
(if i.val < 252 then
303
else
305))
else
(if i.val < 255 then
(if i.val < 254 then
306
else
307)
else
(if i.val < 256 then
308
else
(if i.val < 257 then
309
else
311)))))
else
(if i.val < 267 then
(if i.val < 262 then
(if i.val < 260 then
(if i.val < 259 then
312
else
313)
else
(if i.val < 261 then
314
else
315))
else
(if i.val < 264 then
(if i.val < 263 then
316
else
317)
else
(if i.val < 265 then
318
else
(if i.val < 266 then
319
else
320))))
else
(if i.val < 271 then
(if i.val < 269 then
(if i.val < 268 then
322
else
323)
else
(if i.val < 270 then
324
else
325))
else
(if i.val < 273 then
(if i.val < 272 then
326
else
327)
else
(if i.val < 274 then
328
else
(if i.val < 275 then
329
else
330)))))))))
else
(if i.val < 414 then
(if i.val < 345 then
(if i.val < 310 then
(if i.val < 293 then
(if i.val < 284 then
(if i.val < 280 then
(if i.val < 278 then
(if i.val < 277 then
331
else
332)
else
(if i.val < 279 then
333
else
335))
else
(if i.val < 282 then
(if i.val < 281 then
336
else
338)
else
(if i.val < 283 then
339
else
340)))
else
(if i.val < 288 then
(if i.val < 286 then
(if i.val < 285 then
341
else
342)
else
(if i.val < 287 then
343
else
344))
else
(if i.val < 290 then
(if i.val < 289 then
345
else
346)
else
(if i.val < 291 then
348
else
(if i.val < 292 then
349
else
351)))))
else
(if i.val < 301 then
(if i.val < 297 then
(if i.val < 295 then
(if i.val < 294 then
352
else
353)
else
(if i.val < 296 then
354
else
355))
else
(if i.val < 299 then
(if i.val < 298 then
357
else
358)
else
(if i.val < 300 then
359
else
360)))
else
(if i.val < 305 then
(if i.val < 303 then
(if i.val < 302 then
361
else
362)
else
(if i.val < 304 then
363
else
364))
else
(if i.val < 307 then
(if i.val < 306 then
365
else
366)
else
(if i.val < 308 then
369
else
(if i.val < 309 then
370
else
371))))))
else
(if i.val < 327 then
(if i.val < 318 then
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
372
else
373)
else
(if i.val < 313 then
375
else
377))
else
(if i.val < 316 then
(if i.val < 315 then
378
else
379)
else
(if i.val < 317 then
381
else
382)))
else
(if i.val < 322 then
(if i.val < 320 then
(if i.val < 319 then
384
else
385)
else
(if i.val < 321 then
388
else
390))
else
(if i.val < 324 then
(if i.val < 323 then
392
else
394)
else
(if i.val < 325 then
395
else
(if i.val < 326 then
396
else
397)))))
else
(if i.val < 336 then
(if i.val < 331 then
(if i.val < 329 then
(if i.val < 328 then
398
else
399)
else
(if i.val < 330 then
400
else
401))
else
(if i.val < 333 then
(if i.val < 332 then
403
else
404)
else
(if i.val < 334 then
405
else
(if i.val < 335 then
406
else
407))))
else
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
409
else
411)
else
(if i.val < 339 then
412
else
415))
else
(if i.val < 342 then
(if i.val < 341 then
417
else
418)
else
(if i.val < 343 then
419
else
(if i.val < 344 then
420
else
426)))))))
else
(if i.val < 379 then
(if i.val < 362 then
(if i.val < 353 then
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
427
else
430)
else
(if i.val < 348 then
431
else
435))
else
(if i.val < 351 then
(if i.val < 350 then
437
else
439)
else
(if i.val < 352 then
446
else
453)))
else
(if i.val < 357 then
(if i.val < 355 then
(if i.val < 354 then
455
else
458)
else
(if i.val < 356 then
459
else
463))
else
(if i.val < 359 then
(if i.val < 358 then
464
else
465)
else
(if i.val < 360 then
466
else
(if i.val < 361 then
468
else
469)))))
else
(if i.val < 370 then
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
471
else
475)
else
(if i.val < 365 then
479
else
481))
else
(if i.val < 368 then
(if i.val < 367 then
483
else
485)
else
(if i.val < 369 then
494
else
499)))
else
(if i.val < 374 then
(if i.val < 372 then
(if i.val < 371 then
506
else
508)
else
(if i.val < 373 then
512
else
519))
else
(if i.val < 376 then
(if i.val < 375 then
520
else
522)
else
(if i.val < 377 then
523
else
(if i.val < 378 then
529
else
532))))))
else
(if i.val < 396 then
(if i.val < 387 then
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
533
else
536)
else
(if i.val < 382 then
537
else
538))
else
(if i.val < 385 then
(if i.val < 384 then
539
else
540)
else
(if i.val < 386 then
541
else
542)))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
543
else
544)
else
(if i.val < 390 then
545
else
547))
else
(if i.val < 393 then
(if i.val < 392 then
548
else
549)
else
(if i.val < 394 then
550
else
(if i.val < 395 then
551
else
552)))))
else
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
554
else
555)
else
(if i.val < 399 then
556
else
558))
else
(if i.val < 402 then
(if i.val < 401 then
559
else
561)
else
(if i.val < 403 then
562
else
(if i.val < 404 then
563
else
564))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
565
else
568)
else
(if i.val < 408 then
570
else
572))
else
(if i.val < 411 then
(if i.val < 410 then
575
else
577)
else
(if i.val < 412 then
578
else
(if i.val < 413 then
579
else
580))))))))
else
(if i.val < 483 then
(if i.val < 448 then
(if i.val < 431 then
(if i.val < 422 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
581
else
582)
else
(if i.val < 417 then
583
else
584))
else
(if i.val < 420 then
(if i.val < 419 then
585
else
586)
else
(if i.val < 421 then
587
else
588)))
else
(if i.val < 426 then
(if i.val < 424 then
(if i.val < 423 then
589
else
590)
else
(if i.val < 425 then
592
else
593))
else
(if i.val < 428 then
(if i.val < 427 then
594
else
595)
else
(if i.val < 429 then
597
else
(if i.val < 430 then
598
else
599)))))
else
(if i.val < 439 then
(if i.val < 435 then
(if i.val < 433 then
(if i.val < 432 then
600
else
601)
else
(if i.val < 434 then
603
else
604))
else
(if i.val < 437 then
(if i.val < 436 then
605
else
609)
else
(if i.val < 438 then
610
else
613)))
else
(if i.val < 443 then
(if i.val < 441 then
(if i.val < 440 then
614
else
615)
else
(if i.val < 442 then
616
else
617))
else
(if i.val < 445 then
(if i.val < 444 then
618
else
620)
else
(if i.val < 446 then
624
else
(if i.val < 447 then
628
else
630))))))
else
(if i.val < 465 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
633
else
637)
else
(if i.val < 451 then
638
else
641))
else
(if i.val < 454 then
(if i.val < 453 then
643
else
644)
else
(if i.val < 455 then
650
else
651)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
655
else
656)
else
(if i.val < 459 then
657
else
658))
else
(if i.val < 462 then
(if i.val < 461 then
661
else
662)
else
(if i.val < 463 then
664
else
(if i.val < 464 then
665
else
667)))))
else
(if i.val < 474 then
(if i.val < 469 then
(if i.val < 467 then
(if i.val < 466 then
669
else
670)
else
(if i.val < 468 then
671
else
676))
else
(if i.val < 471 then
(if i.val < 470 then
677
else
682)
else
(if i.val < 472 then
683
else
(if i.val < 473 then
684
else
685))))
else
(if i.val < 478 then
(if i.val < 476 then
(if i.val < 475 then
686
else
690)
else
(if i.val < 477 then
692
else
698))
else
(if i.val < 480 then
(if i.val < 479 then
707
else
710)
else
(if i.val < 481 then
722
else
(if i.val < 482 then
725
else
730)))))))
else
(if i.val < 517 then
(if i.val < 500 then
(if i.val < 491 then
(if i.val < 487 then
(if i.val < 485 then
(if i.val < 484 then
732
else
739)
else
(if i.val < 486 then
755
else
757))
else
(if i.val < 489 then
(if i.val < 488 then
758
else
762)
else
(if i.val < 490 then
781
else
782)))
else
(if i.val < 495 then
(if i.val < 493 then
(if i.val < 492 then
795
else
797)
else
(if i.val < 494 then
800
else
801))
else
(if i.val < 497 then
(if i.val < 496 then
802
else
803)
else
(if i.val < 498 then
805
else
(if i.val < 499 then
806
else
807)))))
else
(if i.val < 508 then
(if i.val < 504 then
(if i.val < 502 then
(if i.val < 501 then
808
else
809)
else
(if i.val < 503 then
811
else
812))
else
(if i.val < 506 then
(if i.val < 505 then
813
else
814)
else
(if i.val < 507 then
817
else
819)))
else
(if i.val < 512 then
(if i.val < 510 then
(if i.val < 509 then
820
else
821)
else
(if i.val < 511 then
823
else
824))
else
(if i.val < 514 then
(if i.val < 513 then
828
else
829)
else
(if i.val < 515 then
830
else
(if i.val < 516 then
831
else
832))))))
else
(if i.val < 534 then
(if i.val < 525 then
(if i.val < 521 then
(if i.val < 519 then
(if i.val < 518 then
834
else
837)
else
(if i.val < 520 then
852
else
855))
else
(if i.val < 523 then
(if i.val < 522 then
858
else
861)
else
(if i.val < 524 then
862
else
866)))
else
(if i.val < 529 then
(if i.val < 527 then
(if i.val < 526 then
869
else
873)
else
(if i.val < 528 then
877
else
878))
else
(if i.val < 531 then
(if i.val < 530 then
883
else
887)
else
(if i.val < 532 then
890
else
(if i.val < 533 then
896
else
899)))))
else
(if i.val < 543 then
(if i.val < 538 then
(if i.val < 536 then
(if i.val < 535 then
900
else
910)
else
(if i.val < 537 then
921
else
923))
else
(if i.val < 540 then
(if i.val < 539 then
934
else
956)
else
(if i.val < 541 then
972
else
(if i.val < 542 then
976
else
987))))
else
(if i.val < 547 then
(if i.val < 545 then
(if i.val < 544 then
989
else
991)
else
(if i.val < 546 then
996
else
998))
else
(if i.val < 549 then
(if i.val < 548 then
999
else
1002)
else
(if i.val < 550 then
1008
else
(if i.val < 551 then
1027
else
1029))))))))))

def g32p_row06_cosetLengths2 : Fin 552 → ℕ :=
  fun i => (if i.val < 276 then
(if i.val < 138 then
(if i.val < 69 then
(if i.val < 34 then
(if i.val < 17 then
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
1
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
(if i.val < 16 then
2
else
2)))))
else
(if i.val < 25 then
(if i.val < 21 then
(if i.val < 19 then
(if i.val < 18 then
2
else
2)
else
(if i.val < 20 then
2
else
2))
else
(if i.val < 23 then
(if i.val < 22 then
2
else
2)
else
(if i.val < 24 then
2
else
2)))
else
(if i.val < 29 then
(if i.val < 27 then
(if i.val < 26 then
2
else
2)
else
(if i.val < 28 then
2
else
2))
else
(if i.val < 31 then
(if i.val < 30 then
2
else
2)
else
(if i.val < 32 then
2
else
(if i.val < 33 then
2
else
2))))))
else
(if i.val < 51 then
(if i.val < 42 then
(if i.val < 38 then
(if i.val < 36 then
(if i.val < 35 then
2
else
2)
else
(if i.val < 37 then
2
else
2))
else
(if i.val < 40 then
(if i.val < 39 then
2
else
2)
else
(if i.val < 41 then
2
else
2)))
else
(if i.val < 46 then
(if i.val < 44 then
(if i.val < 43 then
2
else
2)
else
(if i.val < 45 then
2
else
2))
else
(if i.val < 48 then
(if i.val < 47 then
2
else
1)
else
(if i.val < 49 then
2
else
(if i.val < 50 then
2
else
2)))))
else
(if i.val < 60 then
(if i.val < 55 then
(if i.val < 53 then
(if i.val < 52 then
2
else
2)
else
(if i.val < 54 then
2
else
2))
else
(if i.val < 57 then
(if i.val < 56 then
2
else
2)
else
(if i.val < 58 then
2
else
(if i.val < 59 then
2
else
2))))
else
(if i.val < 64 then
(if i.val < 62 then
(if i.val < 61 then
2
else
2)
else
(if i.val < 63 then
2
else
2))
else
(if i.val < 66 then
(if i.val < 65 then
2
else
2)
else
(if i.val < 67 then
2
else
(if i.val < 68 then
2
else
2)))))))
else
(if i.val < 103 then
(if i.val < 86 then
(if i.val < 77 then
(if i.val < 73 then
(if i.val < 71 then
(if i.val < 70 then
2
else
2)
else
(if i.val < 72 then
2
else
2))
else
(if i.val < 75 then
(if i.val < 74 then
2
else
2)
else
(if i.val < 76 then
2
else
2)))
else
(if i.val < 81 then
(if i.val < 79 then
(if i.val < 78 then
2
else
2)
else
(if i.val < 80 then
2
else
2))
else
(if i.val < 83 then
(if i.val < 82 then
2
else
2)
else
(if i.val < 84 then
2
else
(if i.val < 85 then
2
else
2)))))
else
(if i.val < 94 then
(if i.val < 90 then
(if i.val < 88 then
(if i.val < 87 then
2
else
2)
else
(if i.val < 89 then
2
else
2))
else
(if i.val < 92 then
(if i.val < 91 then
2
else
2)
else
(if i.val < 93 then
2
else
2)))
else
(if i.val < 98 then
(if i.val < 96 then
(if i.val < 95 then
2
else
2)
else
(if i.val < 97 then
2
else
2))
else
(if i.val < 100 then
(if i.val < 99 then
2
else
2)
else
(if i.val < 101 then
2
else
(if i.val < 102 then
2
else
2))))))
else
(if i.val < 120 then
(if i.val < 111 then
(if i.val < 107 then
(if i.val < 105 then
(if i.val < 104 then
2
else
2)
else
(if i.val < 106 then
2
else
2))
else
(if i.val < 109 then
(if i.val < 108 then
2
else
2)
else
(if i.val < 110 then
2
else
2)))
else
(if i.val < 115 then
(if i.val < 113 then
(if i.val < 112 then
2
else
2)
else
(if i.val < 114 then
2
else
2))
else
(if i.val < 117 then
(if i.val < 116 then
2
else
2)
else
(if i.val < 118 then
2
else
(if i.val < 119 then
2
else
2)))))
else
(if i.val < 129 then
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
(if i.val < 128 then
1
else
2))))
else
(if i.val < 133 then
(if i.val < 131 then
(if i.val < 130 then
2
else
2)
else
(if i.val < 132 then
2
else
2))
else
(if i.val < 135 then
(if i.val < 134 then
2
else
2)
else
(if i.val < 136 then
2
else
(if i.val < 137 then
2
else
2))))))))
else
(if i.val < 207 then
(if i.val < 172 then
(if i.val < 155 then
(if i.val < 146 then
(if i.val < 142 then
(if i.val < 140 then
(if i.val < 139 then
2
else
2)
else
(if i.val < 141 then
2
else
2))
else
(if i.val < 144 then
(if i.val < 143 then
1
else
2)
else
(if i.val < 145 then
2
else
2)))
else
(if i.val < 150 then
(if i.val < 148 then
(if i.val < 147 then
2
else
2)
else
(if i.val < 149 then
2
else
2))
else
(if i.val < 152 then
(if i.val < 151 then
2
else
2)
else
(if i.val < 153 then
2
else
(if i.val < 154 then
2
else
2)))))
else
(if i.val < 163 then
(if i.val < 159 then
(if i.val < 157 then
(if i.val < 156 then
2
else
2)
else
(if i.val < 158 then
2
else
2))
else
(if i.val < 161 then
(if i.val < 160 then
2
else
2)
else
(if i.val < 162 then
2
else
2)))
else
(if i.val < 167 then
(if i.val < 165 then
(if i.val < 164 then
2
else
2)
else
(if i.val < 166 then
2
else
2))
else
(if i.val < 169 then
(if i.val < 168 then
2
else
2)
else
(if i.val < 170 then
2
else
(if i.val < 171 then
2
else
2))))))
else
(if i.val < 189 then
(if i.val < 180 then
(if i.val < 176 then
(if i.val < 174 then
(if i.val < 173 then
2
else
2)
else
(if i.val < 175 then
2
else
2))
else
(if i.val < 178 then
(if i.val < 177 then
2
else
2)
else
(if i.val < 179 then
2
else
2)))
else
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
2
else
2)
else
(if i.val < 183 then
2
else
2))
else
(if i.val < 186 then
(if i.val < 185 then
2
else
2)
else
(if i.val < 187 then
2
else
(if i.val < 188 then
2
else
2)))))
else
(if i.val < 198 then
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
2
else
2)
else
(if i.val < 192 then
2
else
2))
else
(if i.val < 195 then
(if i.val < 194 then
2
else
2)
else
(if i.val < 196 then
2
else
(if i.val < 197 then
2
else
2))))
else
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
2
else
2)
else
(if i.val < 201 then
2
else
2))
else
(if i.val < 204 then
(if i.val < 203 then
2
else
2)
else
(if i.val < 205 then
2
else
(if i.val < 206 then
2
else
1)))))))
else
(if i.val < 241 then
(if i.val < 224 then
(if i.val < 215 then
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
2
else
2)
else
(if i.val < 210 then
2
else
2))
else
(if i.val < 213 then
(if i.val < 212 then
2
else
2)
else
(if i.val < 214 then
2
else
2)))
else
(if i.val < 219 then
(if i.val < 217 then
(if i.val < 216 then
2
else
2)
else
(if i.val < 218 then
2
else
2))
else
(if i.val < 221 then
(if i.val < 220 then
2
else
2)
else
(if i.val < 222 then
2
else
(if i.val < 223 then
2
else
2)))))
else
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
(if i.val < 240 then
2
else
2))))))
else
(if i.val < 258 then
(if i.val < 249 then
(if i.val < 245 then
(if i.val < 243 then
(if i.val < 242 then
1
else
2)
else
(if i.val < 244 then
2
else
2))
else
(if i.val < 247 then
(if i.val < 246 then
2
else
2)
else
(if i.val < 248 then
2
else
2)))
else
(if i.val < 253 then
(if i.val < 251 then
(if i.val < 250 then
2
else
2)
else
(if i.val < 252 then
2
else
2))
else
(if i.val < 255 then
(if i.val < 254 then
2
else
2)
else
(if i.val < 256 then
2
else
(if i.val < 257 then
2
else
2)))))
else
(if i.val < 267 then
(if i.val < 262 then
(if i.val < 260 then
(if i.val < 259 then
2
else
2)
else
(if i.val < 261 then
2
else
1))
else
(if i.val < 264 then
(if i.val < 263 then
2
else
2)
else
(if i.val < 265 then
2
else
(if i.val < 266 then
2
else
2))))
else
(if i.val < 271 then
(if i.val < 269 then
(if i.val < 268 then
2
else
2)
else
(if i.val < 270 then
2
else
2))
else
(if i.val < 273 then
(if i.val < 272 then
2
else
2)
else
(if i.val < 274 then
2
else
(if i.val < 275 then
2
else
2)))))))))
else
(if i.val < 414 then
(if i.val < 345 then
(if i.val < 310 then
(if i.val < 293 then
(if i.val < 284 then
(if i.val < 280 then
(if i.val < 278 then
(if i.val < 277 then
2
else
2)
else
(if i.val < 279 then
2
else
2))
else
(if i.val < 282 then
(if i.val < 281 then
2
else
2)
else
(if i.val < 283 then
2
else
2)))
else
(if i.val < 288 then
(if i.val < 286 then
(if i.val < 285 then
2
else
2)
else
(if i.val < 287 then
2
else
2))
else
(if i.val < 290 then
(if i.val < 289 then
2
else
2)
else
(if i.val < 291 then
2
else
(if i.val < 292 then
2
else
2)))))
else
(if i.val < 301 then
(if i.val < 297 then
(if i.val < 295 then
(if i.val < 294 then
2
else
2)
else
(if i.val < 296 then
1
else
2))
else
(if i.val < 299 then
(if i.val < 298 then
2
else
2)
else
(if i.val < 300 then
2
else
2)))
else
(if i.val < 305 then
(if i.val < 303 then
(if i.val < 302 then
2
else
2)
else
(if i.val < 304 then
1
else
2))
else
(if i.val < 307 then
(if i.val < 306 then
2
else
2)
else
(if i.val < 308 then
2
else
(if i.val < 309 then
2
else
2))))))
else
(if i.val < 327 then
(if i.val < 318 then
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
2
else
2)
else
(if i.val < 313 then
2
else
2))
else
(if i.val < 316 then
(if i.val < 315 then
2
else
2)
else
(if i.val < 317 then
2
else
2)))
else
(if i.val < 322 then
(if i.val < 320 then
(if i.val < 319 then
2
else
2)
else
(if i.val < 321 then
2
else
2))
else
(if i.val < 324 then
(if i.val < 323 then
2
else
2)
else
(if i.val < 325 then
2
else
(if i.val < 326 then
2
else
2)))))
else
(if i.val < 336 then
(if i.val < 331 then
(if i.val < 329 then
(if i.val < 328 then
2
else
2)
else
(if i.val < 330 then
2
else
2))
else
(if i.val < 333 then
(if i.val < 332 then
2
else
2)
else
(if i.val < 334 then
2
else
(if i.val < 335 then
2
else
2))))
else
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
(if i.val < 344 then
2
else
2)))))))
else
(if i.val < 379 then
(if i.val < 362 then
(if i.val < 353 then
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
2
else
2)
else
(if i.val < 348 then
1
else
2))
else
(if i.val < 351 then
(if i.val < 350 then
2
else
2)
else
(if i.val < 352 then
2
else
2)))
else
(if i.val < 357 then
(if i.val < 355 then
(if i.val < 354 then
2
else
2)
else
(if i.val < 356 then
2
else
2))
else
(if i.val < 359 then
(if i.val < 358 then
1
else
2)
else
(if i.val < 360 then
2
else
(if i.val < 361 then
2
else
2)))))
else
(if i.val < 370 then
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
2
else
2)
else
(if i.val < 365 then
2
else
2))
else
(if i.val < 368 then
(if i.val < 367 then
2
else
2)
else
(if i.val < 369 then
2
else
2)))
else
(if i.val < 374 then
(if i.val < 372 then
(if i.val < 371 then
1
else
2)
else
(if i.val < 373 then
2
else
2))
else
(if i.val < 376 then
(if i.val < 375 then
2
else
2)
else
(if i.val < 377 then
2
else
(if i.val < 378 then
2
else
2))))))
else
(if i.val < 396 then
(if i.val < 387 then
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
2
else
2)
else
(if i.val < 382 then
2
else
2))
else
(if i.val < 385 then
(if i.val < 384 then
2
else
2)
else
(if i.val < 386 then
2
else
2)))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
2
else
2)
else
(if i.val < 390 then
2
else
2))
else
(if i.val < 393 then
(if i.val < 392 then
2
else
2)
else
(if i.val < 394 then
2
else
(if i.val < 395 then
2
else
2)))))
else
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
2
else
2)
else
(if i.val < 399 then
2
else
2))
else
(if i.val < 402 then
(if i.val < 401 then
2
else
2)
else
(if i.val < 403 then
2
else
(if i.val < 404 then
2
else
2))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
2
else
2)
else
(if i.val < 408 then
2
else
2))
else
(if i.val < 411 then
(if i.val < 410 then
2
else
2)
else
(if i.val < 412 then
2
else
(if i.val < 413 then
2
else
2))))))))
else
(if i.val < 483 then
(if i.val < 448 then
(if i.val < 431 then
(if i.val < 422 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
2
else
2)
else
(if i.val < 417 then
2
else
2))
else
(if i.val < 420 then
(if i.val < 419 then
2
else
2)
else
(if i.val < 421 then
2
else
2)))
else
(if i.val < 426 then
(if i.val < 424 then
(if i.val < 423 then
2
else
2)
else
(if i.val < 425 then
2
else
2))
else
(if i.val < 428 then
(if i.val < 427 then
2
else
2)
else
(if i.val < 429 then
2
else
(if i.val < 430 then
2
else
2)))))
else
(if i.val < 439 then
(if i.val < 435 then
(if i.val < 433 then
(if i.val < 432 then
2
else
2)
else
(if i.val < 434 then
1
else
2))
else
(if i.val < 437 then
(if i.val < 436 then
2
else
2)
else
(if i.val < 438 then
2
else
2)))
else
(if i.val < 443 then
(if i.val < 441 then
(if i.val < 440 then
2
else
2)
else
(if i.val < 442 then
1
else
2))
else
(if i.val < 445 then
(if i.val < 444 then
2
else
2)
else
(if i.val < 446 then
2
else
(if i.val < 447 then
2
else
2))))))
else
(if i.val < 465 then
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
1)
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
1))
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
(if i.val < 464 then
2
else
2)))))
else
(if i.val < 474 then
(if i.val < 469 then
(if i.val < 467 then
(if i.val < 466 then
2
else
2)
else
(if i.val < 468 then
2
else
2))
else
(if i.val < 471 then
(if i.val < 470 then
2
else
2)
else
(if i.val < 472 then
2
else
(if i.val < 473 then
2
else
1))))
else
(if i.val < 478 then
(if i.val < 476 then
(if i.val < 475 then
2
else
2)
else
(if i.val < 477 then
2
else
2))
else
(if i.val < 480 then
(if i.val < 479 then
2
else
2)
else
(if i.val < 481 then
2
else
(if i.val < 482 then
2
else
2)))))))
else
(if i.val < 517 then
(if i.val < 500 then
(if i.val < 491 then
(if i.val < 487 then
(if i.val < 485 then
(if i.val < 484 then
1
else
2)
else
(if i.val < 486 then
1
else
2))
else
(if i.val < 489 then
(if i.val < 488 then
1
else
2)
else
(if i.val < 490 then
2
else
2)))
else
(if i.val < 495 then
(if i.val < 493 then
(if i.val < 492 then
2
else
2)
else
(if i.val < 494 then
1
else
2))
else
(if i.val < 497 then
(if i.val < 496 then
2
else
2)
else
(if i.val < 498 then
2
else
(if i.val < 499 then
2
else
2)))))
else
(if i.val < 508 then
(if i.val < 504 then
(if i.val < 502 then
(if i.val < 501 then
2
else
2)
else
(if i.val < 503 then
2
else
2))
else
(if i.val < 506 then
(if i.val < 505 then
2
else
2)
else
(if i.val < 507 then
2
else
2)))
else
(if i.val < 512 then
(if i.val < 510 then
(if i.val < 509 then
2
else
2)
else
(if i.val < 511 then
2
else
2))
else
(if i.val < 514 then
(if i.val < 513 then
2
else
2)
else
(if i.val < 515 then
2
else
(if i.val < 516 then
2
else
2))))))
else
(if i.val < 534 then
(if i.val < 525 then
(if i.val < 521 then
(if i.val < 519 then
(if i.val < 518 then
2
else
2)
else
(if i.val < 520 then
2
else
2))
else
(if i.val < 523 then
(if i.val < 522 then
2
else
2)
else
(if i.val < 524 then
2
else
2)))
else
(if i.val < 529 then
(if i.val < 527 then
(if i.val < 526 then
2
else
2)
else
(if i.val < 528 then
1
else
2))
else
(if i.val < 531 then
(if i.val < 530 then
2
else
2)
else
(if i.val < 532 then
2
else
(if i.val < 533 then
2
else
2)))))
else
(if i.val < 543 then
(if i.val < 538 then
(if i.val < 536 then
(if i.val < 535 then
2
else
2)
else
(if i.val < 537 then
2
else
2))
else
(if i.val < 540 then
(if i.val < 539 then
2
else
2)
else
(if i.val < 541 then
2
else
(if i.val < 542 then
1
else
2))))
else
(if i.val < 547 then
(if i.val < 545 then
(if i.val < 544 then
2
else
2)
else
(if i.val < 546 then
2
else
2))
else
(if i.val < 549 then
(if i.val < 548 then
2
else
1)
else
(if i.val < 550 then
2
else
(if i.val < 551 then
2
else
2))))))))))

def g32p_row06_cosetCycleNodes2 : Fin 552 → List ℕ :=
  fun i => (if i.val < 276 then
(if i.val < 138 then
(if i.val < 69 then
(if i.val < 34 then
(if i.val < 17 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
[0, 444]
else
[1, 566])
else
(if i.val < 3 then
[2, 546]
else
[3, 779]))
else
(if i.val < 6 then
(if i.val < 5 then
[4, 96]
else
[5, 942])
else
(if i.val < 7 then
[6]
else
[7, 159])))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
[8, 148]
else
[9, 154])
else
(if i.val < 11 then
[10, 223]
else
[11, 907]))
else
(if i.val < 14 then
(if i.val < 13 then
[12, 285]
else
[13, 983])
else
(if i.val < 15 then
[14, 280]
else
(if i.val < 16 then
[15, 227]
else
[16, 171])))))
else
(if i.val < 25 then
(if i.val < 21 then
(if i.val < 19 then
(if i.val < 18 then
[17, 962]
else
[18, 239])
else
(if i.val < 20 then
[19, 452]
else
[20, 423]))
else
(if i.val < 23 then
(if i.val < 22 then
[21, 380]
else
[22, 421])
else
(if i.val < 24 then
[23, 491]
else
[24, 334])))
else
(if i.val < 29 then
(if i.val < 27 then
(if i.val < 26 then
[25, 422]
else
[26, 347])
else
(if i.val < 28 then
[27, 1063]
else
[28, 449]))
else
(if i.val < 31 then
(if i.val < 30 then
[29, 310]
else
[30, 985])
else
(if i.val < 32 then
[31, 1022]
else
(if i.val < 33 then
[32, 1028]
else
[33, 451]))))))
else
(if i.val < 51 then
(if i.val < 42 then
(if i.val < 38 then
(if i.val < 36 then
(if i.val < 35 then
[34, 416]
else
[35, 1010])
else
(if i.val < 37 then
[36, 1052]
else
[37, 1054]))
else
(if i.val < 40 then
(if i.val < 39 then
[38, 448]
else
[39, 534])
else
(if i.val < 41 then
[40, 473]
else
[41, 443])))
else
(if i.val < 46 then
(if i.val < 44 then
(if i.val < 43 then
[42, 467]
else
[43, 500])
else
(if i.val < 45 then
[44, 356]
else
[45, 1062]))
else
(if i.val < 48 then
(if i.val < 47 then
[46, 54]
else
[47])
else
(if i.val < 49 then
[48, 474]
else
(if i.val < 50 then
[49, 456]
else
[50, 513])))))
else
(if i.val < 60 then
(if i.val < 55 then
(if i.val < 53 then
(if i.val < 52 then
[51, 367]
else
[52, 424])
else
(if i.val < 54 then
[53, 429]
else
[55, 102]))
else
(if i.val < 57 then
(if i.val < 56 then
[56, 649]
else
[57, 61])
else
(if i.val < 58 then
[58, 695]
else
(if i.val < 59 then
[59, 126]
else
[60, 92]))))
else
(if i.val < 64 then
(if i.val < 62 then
(if i.val < 61 then
[62, 715]
else
[63, 632])
else
(if i.val < 63 then
[64, 629]
else
[65, 84]))
else
(if i.val < 66 then
(if i.val < 65 then
[66, 756]
else
[67, 668])
else
(if i.val < 67 then
[68, 747]
else
(if i.val < 68 then
[69, 602]
else
[70, 642])))))))
else
(if i.val < 103 then
(if i.val < 86 then
(if i.val < 77 then
(if i.val < 73 then
(if i.val < 71 then
(if i.val < 70 then
[71, 793]
else
[72, 607])
else
(if i.val < 72 then
[73, 130]
else
[74, 712]))
else
(if i.val < 75 then
(if i.val < 74 then
[75, 560]
else
[76, 663])
else
(if i.val < 76 then
[77, 109]
else
[78, 99])))
else
(if i.val < 81 then
(if i.val < 79 then
(if i.val < 78 then
[79, 1076]
else
[80, 619])
else
(if i.val < 80 then
[81, 729]
else
[82, 573]))
else
(if i.val < 83 then
(if i.val < 82 then
[83, 125]
else
[85, 108])
else
(if i.val < 84 then
[86, 576]
else
(if i.val < 85 then
[87, 557]
else
[88, 687])))))
else
(if i.val < 94 then
(if i.val < 90 then
(if i.val < 88 then
(if i.val < 87 then
[89, 723]
else
[90, 705])
else
(if i.val < 89 then
[91, 646]
else
[93, 745]))
else
(if i.val < 92 then
(if i.val < 91 then
[94, 571]
else
[95, 648])
else
(if i.val < 93 then
[97, 727]
else
[98, 790])))
else
(if i.val < 98 then
(if i.val < 96 then
(if i.val < 95 then
[100, 717]
else
[101, 760])
else
(if i.val < 97 then
[103, 713]
else
[104, 697]))
else
(if i.val < 100 then
(if i.val < 99 then
[105, 117]
else
[106, 768])
else
(if i.val < 101 then
[107, 113]
else
(if i.val < 102 then
[110, 744]
else
[111, 652]))))))
else
(if i.val < 120 then
(if i.val < 111 then
(if i.val < 107 then
(if i.val < 105 then
(if i.val < 104 then
[112, 786]
else
[114, 740])
else
(if i.val < 106 then
[115, 639]
else
[116, 714]))
else
(if i.val < 109 then
(if i.val < 108 then
[118, 1073]
else
[119, 591])
else
(if i.val < 110 then
[120, 708]
else
[121, 750])))
else
(if i.val < 115 then
(if i.val < 113 then
(if i.val < 112 then
[122, 608]
else
[123, 694])
else
(if i.val < 114 then
[124, 625]
else
[127, 553]))
else
(if i.val < 117 then
(if i.val < 116 then
[128, 763]
else
[129, 791])
else
(if i.val < 118 then
[131, 776]
else
(if i.val < 119 then
[132, 784]
else
[133, 1074])))))
else
(if i.val < 129 then
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
[134, 574]
else
[135, 773])
else
(if i.val < 123 then
[136, 653]
else
[137, 699]))
else
(if i.val < 126 then
(if i.val < 125 then
[138, 922]
else
[139, 864])
else
(if i.val < 127 then
[140, 920]
else
(if i.val < 128 then
[141]
else
[142, 868]))))
else
(if i.val < 133 then
(if i.val < 131 then
(if i.val < 130 then
[143, 924]
else
[144, 291])
else
(if i.val < 132 then
[145, 273]
else
[146, 186]))
else
(if i.val < 135 then
(if i.val < 134 then
[147, 191]
else
[149, 946])
else
(if i.val < 136 then
[150, 841]
else
(if i.val < 137 then
[151, 914]
else
[152, 894]))))))))
else
(if i.val < 207 then
(if i.val < 172 then
(if i.val < 155 then
(if i.val < 146 then
(if i.val < 142 then
(if i.val < 140 then
(if i.val < 139 then
[153, 859]
else
[155, 854])
else
(if i.val < 141 then
[156, 893]
else
[157, 208]))
else
(if i.val < 144 then
(if i.val < 143 then
[158]
else
[160, 218])
else
(if i.val < 145 then
[161, 865]
else
[162, 253])))
else
(if i.val < 150 then
(if i.val < 148 then
(if i.val < 147 then
[163, 198]
else
[164, 267])
else
(if i.val < 149 then
[165, 217]
else
[166, 912]))
else
(if i.val < 152 then
(if i.val < 151 then
[167, 244]
else
[168, 247])
else
(if i.val < 153 then
[169, 833]
else
(if i.val < 154 then
[170, 944]
else
[172, 261])))))
else
(if i.val < 163 then
(if i.val < 159 then
(if i.val < 157 then
(if i.val < 156 then
[173, 897]
else
[174, 254])
else
(if i.val < 158 then
[175, 840]
else
[176, 964]))
else
(if i.val < 161 then
(if i.val < 160 then
[177, 871]
else
[178, 870])
else
(if i.val < 162 then
[179, 810]
else
[180, 839])))
else
(if i.val < 167 then
(if i.val < 165 then
(if i.val < 164 then
[181, 290]
else
[182, 880])
else
(if i.val < 166 then
[183, 913]
else
[184, 892]))
else
(if i.val < 169 then
(if i.val < 168 then
[185, 796]
else
[187, 981])
else
(if i.val < 170 then
[188, 948]
else
(if i.val < 171 then
[189, 263]
else
[190, 849]))))))
else
(if i.val < 189 then
(if i.val < 180 then
(if i.val < 176 then
(if i.val < 174 then
(if i.val < 173 then
[192, 235]
else
[193, 968])
else
(if i.val < 175 then
[194, 973]
else
[195, 842]))
else
(if i.val < 178 then
(if i.val < 177 then
[196, 971]
else
[197, 826])
else
(if i.val < 179 then
[199, 874]
else
[200, 815])))
else
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
[201, 853]
else
[202, 919])
else
(if i.val < 183 then
[203, 969]
else
[204, 258]))
else
(if i.val < 186 then
(if i.val < 185 then
[205, 925]
else
[206, 916])
else
(if i.val < 187 then
[207, 945]
else
(if i.val < 188 then
[209, 804]
else
[210, 902])))))
else
(if i.val < 198 then
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
[211, 904]
else
[212, 959])
else
(if i.val < 192 then
[213, 850]
else
[214, 276]))
else
(if i.val < 195 then
(if i.val < 194 then
[215, 283]
else
[216, 242])
else
(if i.val < 196 then
[219, 268]
else
(if i.val < 197 then
[220, 818]
else
[221, 288]))))
else
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
[222, 951]
else
[224, 836])
else
(if i.val < 201 then
[225, 965]
else
[226, 955]))
else
(if i.val < 204 then
(if i.val < 203 then
[228, 845]
else
[229, 277])
else
(if i.val < 205 then
[230, 915]
else
(if i.val < 206 then
[231, 980]
else
[232])))))))
else
(if i.val < 241 then
(if i.val < 224 then
(if i.val < 215 then
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
[233, 947]
else
[234, 246])
else
(if i.val < 210 then
[236, 939]
else
[237, 974]))
else
(if i.val < 213 then
(if i.val < 212 then
[238, 867]
else
[240, 264])
else
(if i.val < 214 then
[241, 851]
else
[243, 863])))
else
(if i.val < 219 then
(if i.val < 217 then
(if i.val < 216 then
[245, 901]
else
[248, 847])
else
(if i.val < 218 then
[249, 886]
else
[250, 289]))
else
(if i.val < 221 then
(if i.val < 220 then
[251, 827]
else
[252, 856])
else
(if i.val < 222 then
[255, 822]
else
(if i.val < 223 then
[256, 838]
else
[257, 292])))))
else
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
[259, 928]
else
[260, 905])
else
(if i.val < 227 then
[262, 266]
else
[265, 935]))
else
(if i.val < 230 then
(if i.val < 229 then
[269, 967]
else
[270, 979])
else
(if i.val < 231 then
[271, 937]
else
[272, 882])))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
[274, 933]
else
[275, 816])
else
(if i.val < 235 then
[278, 881]
else
[279, 982]))
else
(if i.val < 238 then
(if i.val < 237 then
[281, 798]
else
[282, 825])
else
(if i.val < 239 then
[284, 799]
else
(if i.val < 240 then
[286, 835]
else
[287, 903]))))))
else
(if i.val < 258 then
(if i.val < 249 then
(if i.val < 245 then
(if i.val < 243 then
(if i.val < 242 then
[293]
else
[294, 848])
else
(if i.val < 244 then
[295, 477]
else
[296, 525]))
else
(if i.val < 247 then
(if i.val < 246 then
[297, 527]
else
[298, 1060])
else
(if i.val < 248 then
[299, 413]
else
[300, 1046])))
else
(if i.val < 253 then
(if i.val < 251 then
(if i.val < 250 then
[301, 304]
else
[302, 488])
else
(if i.val < 252 then
[303, 368]
else
[305, 521]))
else
(if i.val < 255 then
(if i.val < 254 then
[306, 321]
else
[307, 387])
else
(if i.val < 256 then
[308, 530]
else
(if i.val < 257 then
[309, 984]
else
[311, 505])))))
else
(if i.val < 267 then
(if i.val < 262 then
(if i.val < 260 then
(if i.val < 259 then
[312, 376]
else
[313, 374])
else
(if i.val < 261 then
[314, 337]
else
[315]))
else
(if i.val < 264 then
(if i.val < 263 then
[316, 1032]
else
[317, 1053])
else
(if i.val < 265 then
[318, 433]
else
(if i.val < 266 then
[319, 1055]
else
[320, 1050]))))
else
(if i.val < 271 then
(if i.val < 269 then
(if i.val < 268 then
[322, 470]
else
[323, 393])
else
(if i.val < 270 then
[324, 350]
else
[325, 383]))
else
(if i.val < 273 then
(if i.val < 272 then
[326, 436]
else
[327, 462])
else
(if i.val < 274 then
[328, 450]
else
(if i.val < 275 then
[329, 1001]
else
[330, 410])))))))))
else
(if i.val < 414 then
(if i.val < 345 then
(if i.val < 310 then
(if i.val < 293 then
(if i.val < 284 then
(if i.val < 280 then
(if i.val < 278 then
(if i.val < 277 then
[331, 526]
else
[332, 445])
else
(if i.val < 279 then
[333, 484]
else
[335, 501]))
else
(if i.val < 282 then
(if i.val < 281 then
[336, 993]
else
[338, 517])
else
(if i.val < 283 then
[339, 1021]
else
[340, 391])))
else
(if i.val < 288 then
(if i.val < 286 then
(if i.val < 285 then
[341, 386]
else
[342, 1003])
else
(if i.val < 287 then
[343, 510]
else
[344, 515]))
else
(if i.val < 290 then
(if i.val < 289 then
[345, 440]
else
[346, 486])
else
(if i.val < 291 then
[348, 502]
else
(if i.val < 292 then
[349, 408]
else
[351, 414])))))
else
(if i.val < 301 then
(if i.val < 297 then
(if i.val < 295 then
(if i.val < 294 then
[352, 1061]
else
[353, 442])
else
(if i.val < 296 then
[354]
else
[355, 503]))
else
(if i.val < 299 then
(if i.val < 298 then
[357, 1051]
else
[358, 447])
else
(if i.val < 300 then
[359, 1000]
else
[360, 524])))
else
(if i.val < 305 then
(if i.val < 303 then
(if i.val < 302 then
[361, 988]
else
[362, 492])
else
(if i.val < 304 then
[363]
else
[364, 1040]))
else
(if i.val < 307 then
(if i.val < 306 then
[365, 528]
else
[366, 1013])
else
(if i.val < 308 then
[369, 1016]
else
(if i.val < 309 then
[370, 402]
else
[371, 1041]))))))
else
(if i.val < 327 then
(if i.val < 318 then
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
[372, 1018]
else
[373, 1017])
else
(if i.val < 313 then
[375, 1047]
else
[377, 1035]))
else
(if i.val < 316 then
(if i.val < 315 then
[378, 535]
else
[379, 1025])
else
(if i.val < 317 then
[381, 389]
else
[382, 490])))
else
(if i.val < 322 then
(if i.val < 320 then
(if i.val < 319 then
[384, 1034]
else
[385, 438])
else
(if i.val < 321 then
[388, 1019]
else
[390, 1030]))
else
(if i.val < 324 then
(if i.val < 323 then
[392, 441]
else
[394, 986])
else
(if i.val < 325 then
[395, 995]
else
(if i.val < 326 then
[396, 428]
else
[397, 496])))))
else
(if i.val < 336 then
(if i.val < 331 then
(if i.val < 329 then
(if i.val < 328 then
[398, 1023]
else
[399, 509])
else
(if i.val < 330 then
[400, 1024]
else
[401, 478]))
else
(if i.val < 333 then
(if i.val < 332 then
[403, 425]
else
[404, 454])
else
(if i.val < 334 then
[405, 487]
else
(if i.val < 335 then
[406, 1049]
else
[407, 432]))))
else
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
[409, 1005]
else
[411, 434])
else
(if i.val < 339 then
[412, 507]
else
[415, 992]))
else
(if i.val < 342 then
(if i.val < 341 then
[417, 1033]
else
[418, 460])
else
(if i.val < 343 then
[419, 1007]
else
(if i.val < 344 then
[420, 1004]
else
[426, 1059])))))))
else
(if i.val < 379 then
(if i.val < 362 then
(if i.val < 353 then
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
[427, 493]
else
[430, 1037])
else
(if i.val < 348 then
[431]
else
[435, 457]))
else
(if i.val < 351 then
(if i.val < 350 then
[437, 489]
else
[439, 461])
else
(if i.val < 352 then
[446, 1006]
else
[453, 482])))
else
(if i.val < 357 then
(if i.val < 355 then
(if i.val < 354 then
[455, 498]
else
[458, 495])
else
(if i.val < 356 then
[459, 476]
else
[463, 994]))
else
(if i.val < 359 then
(if i.val < 358 then
[464]
else
[465, 480])
else
(if i.val < 360 then
[466, 511]
else
(if i.val < 361 then
[468, 531]
else
[469, 472])))))
else
(if i.val < 370 then
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
[471, 518]
else
[475, 514])
else
(if i.val < 365 then
[479, 497]
else
[481, 1026]))
else
(if i.val < 368 then
(if i.val < 367 then
[483, 504]
else
[485, 1036])
else
(if i.val < 369 then
[494, 516]
else
[499, 990])))
else
(if i.val < 374 then
(if i.val < 372 then
(if i.val < 371 then
[506]
else
[508, 1064])
else
(if i.val < 373 then
[512, 997]
else
[519, 1031]))
else
(if i.val < 376 then
(if i.val < 375 then
[520, 1058]
else
[522, 1009])
else
(if i.val < 377 then
[523, 1045]
else
(if i.val < 378 then
[529, 1020]
else
[532, 1015]))))))
else
(if i.val < 396 then
(if i.val < 387 then
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
[533, 1039]
else
[536, 1038])
else
(if i.val < 382 then
[537, 788]
else
[538, 741]))
else
(if i.val < 385 then
(if i.val < 384 then
[539, 700]
else
[540, 1067])
else
(if i.val < 386 then
[541, 736]
else
[542, 696])))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
[543, 1078]
else
[544, 720])
else
(if i.val < 390 then
[545, 765]
else
[547, 611]))
else
(if i.val < 393 then
(if i.val < 392 then
[548, 706]
else
[549, 627])
else
(if i.val < 394 then
[550, 774]
else
(if i.val < 395 then
[551, 738]
else
[552, 567])))))
else
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
[554, 569]
else
[555, 626])
else
(if i.val < 399 then
[556, 678]
else
[558, 623]))
else
(if i.val < 402 then
(if i.val < 401 then
[559, 748]
else
[561, 701])
else
(if i.val < 403 then
[562, 634]
else
(if i.val < 404 then
[563, 622]
else
[564, 679]))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
[565, 681]
else
[568, 675])
else
(if i.val < 408 then
[570, 770]
else
[572, 659]))
else
(if i.val < 411 then
(if i.val < 410 then
[575, 635]
else
[577, 702])
else
(if i.val < 412 then
[578, 673]
else
(if i.val < 413 then
[579, 660]
else
[580, 724]))))))))
else
(if i.val < 483 then
(if i.val < 448 then
(if i.val < 431 then
(if i.val < 422 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
[581, 680]
else
[582, 612])
else
(if i.val < 417 then
[583, 704]
else
[584, 711]))
else
(if i.val < 420 then
(if i.val < 419 then
[585, 688]
else
[586, 731])
else
(if i.val < 421 then
[587, 1077]
else
[588, 645])))
else
(if i.val < 426 then
(if i.val < 424 then
(if i.val < 423 then
[589, 754]
else
[590, 636])
else
(if i.val < 425 then
[592, 674]
else
[593, 596]))
else
(if i.val < 428 then
(if i.val < 427 then
[594, 721]
else
[595, 640])
else
(if i.val < 429 then
[597, 693]
else
(if i.val < 430 then
[598, 654]
else
[599, 737])))))
else
(if i.val < 439 then
(if i.val < 435 then
(if i.val < 433 then
(if i.val < 432 then
[600, 778]
else
[601, 1069])
else
(if i.val < 434 then
[603]
else
[604, 728]))
else
(if i.val < 437 then
(if i.val < 436 then
[605, 606]
else
[609, 759])
else
(if i.val < 438 then
[610, 718]
else
[613, 666])))
else
(if i.val < 443 then
(if i.val < 441 then
(if i.val < 440 then
[614, 752]
else
[615, 621])
else
(if i.val < 442 then
[616]
else
[617, 743]))
else
(if i.val < 445 then
(if i.val < 444 then
[618, 742]
else
[620, 769])
else
(if i.val < 446 then
[624, 726]
else
(if i.val < 447 then
[628, 761]
else
[630, 631]))))))
else
(if i.val < 465 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
[633, 709]
else
[637, 719])
else
(if i.val < 451 then
[638, 766]
else
[641, 733]))
else
(if i.val < 454 then
(if i.val < 453 then
[643, 647]
else
[644])
else
(if i.val < 455 then
[650, 691]
else
[651, 746])))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
[655, 1068]
else
[656, 1072])
else
(if i.val < 459 then
[657, 672]
else
[658]))
else
(if i.val < 462 then
(if i.val < 461 then
[661, 775]
else
[662, 787])
else
(if i.val < 463 then
[664, 749]
else
(if i.val < 464 then
[665, 1065]
else
[667, 777])))))
else
(if i.val < 474 then
(if i.val < 469 then
(if i.val < 467 then
(if i.val < 466 then
[669, 735]
else
[670, 1075])
else
(if i.val < 468 then
[671, 780]
else
[676, 1079]))
else
(if i.val < 471 then
(if i.val < 470 then
[677, 716]
else
[682, 771])
else
(if i.val < 472 then
[683, 1066]
else
(if i.val < 473 then
[684, 689]
else
[685]))))
else
(if i.val < 478 then
(if i.val < 476 then
(if i.val < 475 then
[686, 794]
else
[690, 734])
else
(if i.val < 477 then
[692, 789]
else
[698, 703]))
else
(if i.val < 480 then
(if i.val < 479 then
[707, 783]
else
[710, 772])
else
(if i.val < 481 then
[722, 764]
else
(if i.val < 482 then
[725, 751]
else
[730, 753])))))))
else
(if i.val < 517 then
(if i.val < 500 then
(if i.val < 491 then
(if i.val < 487 then
(if i.val < 485 then
(if i.val < 484 then
[732]
else
[739, 1071])
else
(if i.val < 486 then
[755]
else
[757, 785]))
else
(if i.val < 489 then
(if i.val < 488 then
[758]
else
[762, 767])
else
(if i.val < 490 then
[781, 792]
else
[782, 1070])))
else
(if i.val < 495 then
(if i.val < 493 then
(if i.val < 492 then
[795, 953]
else
[797, 932])
else
(if i.val < 494 then
[800]
else
[801, 857]))
else
(if i.val < 497 then
(if i.val < 496 then
[802, 875]
else
[803, 936])
else
(if i.val < 498 then
[805, 876]
else
(if i.val < 499 then
[806, 927]
else
[807, 950])))))
else
(if i.val < 508 then
(if i.val < 504 then
(if i.val < 502 then
(if i.val < 501 then
[808, 895]
else
[809, 977])
else
(if i.val < 503 then
[811, 879]
else
[812, 958]))
else
(if i.val < 506 then
(if i.val < 505 then
[813, 961]
else
[814, 917])
else
(if i.val < 507 then
[817, 908]
else
[819, 943])))
else
(if i.val < 512 then
(if i.val < 510 then
(if i.val < 509 then
[820, 844]
else
[821, 930])
else
(if i.val < 511 then
[823, 970]
else
[824, 843]))
else
(if i.val < 514 then
(if i.val < 513 then
[828, 860]
else
[829, 918])
else
(if i.val < 515 then
[830, 906]
else
(if i.val < 516 then
[831, 846]
else
[832, 872]))))))
else
(if i.val < 534 then
(if i.val < 525 then
(if i.val < 521 then
(if i.val < 519 then
(if i.val < 518 then
[834, 891]
else
[837, 963])
else
(if i.val < 520 then
[852, 931]
else
[855, 941]))
else
(if i.val < 523 then
(if i.val < 522 then
[858, 954]
else
[861, 909])
else
(if i.val < 524 then
[862, 888]
else
[866, 884])))
else
(if i.val < 529 then
(if i.val < 527 then
(if i.val < 526 then
[869, 926]
else
[873, 957])
else
(if i.val < 528 then
[877]
else
[878, 978]))
else
(if i.val < 531 then
(if i.val < 530 then
[883, 885]
else
[887, 889])
else
(if i.val < 532 then
[890, 966]
else
(if i.val < 533 then
[896, 898]
else
[899, 940])))))
else
(if i.val < 543 then
(if i.val < 538 then
(if i.val < 536 then
(if i.val < 535 then
[900, 911]
else
[910, 952])
else
(if i.val < 537 then
[921, 929]
else
[923, 949]))
else
(if i.val < 540 then
(if i.val < 539 then
[934, 938]
else
[956, 960])
else
(if i.val < 541 then
[972, 975]
else
(if i.val < 542 then
[976]
else
[987, 1057]))))
else
(if i.val < 547 then
(if i.val < 545 then
(if i.val < 544 then
[989, 1011]
else
[991, 1014])
else
(if i.val < 546 then
[996, 1012]
else
[998, 1048]))
else
(if i.val < 549 then
(if i.val < 548 then
[999, 1056]
else
[1002])
else
(if i.val < 550 then
[1008, 1043]
else
(if i.val < 551 then
[1027, 1044]
else
[1029, 1042]))))))))))

def g32p_row06_cosetCycles2 : List (List ℕ) :=
  List.ofFn g32p_row06_cosetCycleNodes2

def g32p_row06_cosetMonodromies2 : Fin 552 → Fin 144 :=
  fun i => (if i.val < 276 then
(if i.val < 138 then
(if i.val < 69 then
(if i.val < 34 then
(if i.val < 17 then
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
12
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
(if i.val < 16 then
0
else
0)))))
else
(if i.val < 25 then
(if i.val < 21 then
(if i.val < 19 then
(if i.val < 18 then
0
else
0)
else
(if i.val < 20 then
0
else
0))
else
(if i.val < 23 then
(if i.val < 22 then
0
else
0)
else
(if i.val < 24 then
0
else
0)))
else
(if i.val < 29 then
(if i.val < 27 then
(if i.val < 26 then
0
else
0)
else
(if i.val < 28 then
0
else
0))
else
(if i.val < 31 then
(if i.val < 30 then
0
else
0)
else
(if i.val < 32 then
0
else
(if i.val < 33 then
0
else
0))))))
else
(if i.val < 51 then
(if i.val < 42 then
(if i.val < 38 then
(if i.val < 36 then
(if i.val < 35 then
0
else
0)
else
(if i.val < 37 then
0
else
0))
else
(if i.val < 40 then
(if i.val < 39 then
0
else
0)
else
(if i.val < 41 then
0
else
0)))
else
(if i.val < 46 then
(if i.val < 44 then
(if i.val < 43 then
0
else
0)
else
(if i.val < 45 then
0
else
0))
else
(if i.val < 48 then
(if i.val < 47 then
0
else
12)
else
(if i.val < 49 then
0
else
(if i.val < 50 then
0
else
0)))))
else
(if i.val < 60 then
(if i.val < 55 then
(if i.val < 53 then
(if i.val < 52 then
0
else
0)
else
(if i.val < 54 then
0
else
0))
else
(if i.val < 57 then
(if i.val < 56 then
0
else
0)
else
(if i.val < 58 then
0
else
(if i.val < 59 then
0
else
0))))
else
(if i.val < 64 then
(if i.val < 62 then
(if i.val < 61 then
0
else
0)
else
(if i.val < 63 then
0
else
0))
else
(if i.val < 66 then
(if i.val < 65 then
0
else
0)
else
(if i.val < 67 then
0
else
(if i.val < 68 then
0
else
0)))))))
else
(if i.val < 103 then
(if i.val < 86 then
(if i.val < 77 then
(if i.val < 73 then
(if i.val < 71 then
(if i.val < 70 then
0
else
0)
else
(if i.val < 72 then
0
else
0))
else
(if i.val < 75 then
(if i.val < 74 then
0
else
0)
else
(if i.val < 76 then
0
else
0)))
else
(if i.val < 81 then
(if i.val < 79 then
(if i.val < 78 then
0
else
0)
else
(if i.val < 80 then
0
else
0))
else
(if i.val < 83 then
(if i.val < 82 then
0
else
0)
else
(if i.val < 84 then
0
else
(if i.val < 85 then
0
else
0)))))
else
(if i.val < 94 then
(if i.val < 90 then
(if i.val < 88 then
(if i.val < 87 then
0
else
0)
else
(if i.val < 89 then
0
else
0))
else
(if i.val < 92 then
(if i.val < 91 then
0
else
0)
else
(if i.val < 93 then
0
else
0)))
else
(if i.val < 98 then
(if i.val < 96 then
(if i.val < 95 then
0
else
0)
else
(if i.val < 97 then
0
else
0))
else
(if i.val < 100 then
(if i.val < 99 then
0
else
0)
else
(if i.val < 101 then
0
else
(if i.val < 102 then
0
else
0))))))
else
(if i.val < 120 then
(if i.val < 111 then
(if i.val < 107 then
(if i.val < 105 then
(if i.val < 104 then
0
else
0)
else
(if i.val < 106 then
0
else
0))
else
(if i.val < 109 then
(if i.val < 108 then
0
else
0)
else
(if i.val < 110 then
0
else
0)))
else
(if i.val < 115 then
(if i.val < 113 then
(if i.val < 112 then
0
else
0)
else
(if i.val < 114 then
0
else
0))
else
(if i.val < 117 then
(if i.val < 116 then
0
else
0)
else
(if i.val < 118 then
0
else
(if i.val < 119 then
0
else
0)))))
else
(if i.val < 129 then
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
(if i.val < 128 then
5
else
0))))
else
(if i.val < 133 then
(if i.val < 131 then
(if i.val < 130 then
0
else
0)
else
(if i.val < 132 then
0
else
0))
else
(if i.val < 135 then
(if i.val < 134 then
0
else
0)
else
(if i.val < 136 then
0
else
(if i.val < 137 then
0
else
0))))))))
else
(if i.val < 207 then
(if i.val < 172 then
(if i.val < 155 then
(if i.val < 146 then
(if i.val < 142 then
(if i.val < 140 then
(if i.val < 139 then
0
else
0)
else
(if i.val < 141 then
0
else
0))
else
(if i.val < 144 then
(if i.val < 143 then
5
else
0)
else
(if i.val < 145 then
0
else
0)))
else
(if i.val < 150 then
(if i.val < 148 then
(if i.val < 147 then
0
else
0)
else
(if i.val < 149 then
0
else
0))
else
(if i.val < 152 then
(if i.val < 151 then
0
else
0)
else
(if i.val < 153 then
0
else
(if i.val < 154 then
0
else
0)))))
else
(if i.val < 163 then
(if i.val < 159 then
(if i.val < 157 then
(if i.val < 156 then
0
else
0)
else
(if i.val < 158 then
0
else
0))
else
(if i.val < 161 then
(if i.val < 160 then
0
else
0)
else
(if i.val < 162 then
0
else
0)))
else
(if i.val < 167 then
(if i.val < 165 then
(if i.val < 164 then
0
else
0)
else
(if i.val < 166 then
0
else
0))
else
(if i.val < 169 then
(if i.val < 168 then
0
else
0)
else
(if i.val < 170 then
0
else
(if i.val < 171 then
0
else
0))))))
else
(if i.val < 189 then
(if i.val < 180 then
(if i.val < 176 then
(if i.val < 174 then
(if i.val < 173 then
0
else
0)
else
(if i.val < 175 then
0
else
0))
else
(if i.val < 178 then
(if i.val < 177 then
0
else
0)
else
(if i.val < 179 then
0
else
0)))
else
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
0
else
0)
else
(if i.val < 183 then
0
else
0))
else
(if i.val < 186 then
(if i.val < 185 then
0
else
0)
else
(if i.val < 187 then
0
else
(if i.val < 188 then
0
else
0)))))
else
(if i.val < 198 then
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
0
else
0)
else
(if i.val < 192 then
0
else
0))
else
(if i.val < 195 then
(if i.val < 194 then
0
else
0)
else
(if i.val < 196 then
0
else
(if i.val < 197 then
0
else
0))))
else
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
0
else
0)
else
(if i.val < 201 then
0
else
0))
else
(if i.val < 204 then
(if i.val < 203 then
0
else
0)
else
(if i.val < 205 then
0
else
(if i.val < 206 then
0
else
5)))))))
else
(if i.val < 241 then
(if i.val < 224 then
(if i.val < 215 then
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
0
else
0)
else
(if i.val < 210 then
0
else
0))
else
(if i.val < 213 then
(if i.val < 212 then
0
else
0)
else
(if i.val < 214 then
0
else
0)))
else
(if i.val < 219 then
(if i.val < 217 then
(if i.val < 216 then
0
else
0)
else
(if i.val < 218 then
0
else
0))
else
(if i.val < 221 then
(if i.val < 220 then
0
else
0)
else
(if i.val < 222 then
0
else
(if i.val < 223 then
0
else
0)))))
else
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
(if i.val < 240 then
0
else
0))))))
else
(if i.val < 258 then
(if i.val < 249 then
(if i.val < 245 then
(if i.val < 243 then
(if i.val < 242 then
12
else
0)
else
(if i.val < 244 then
0
else
0))
else
(if i.val < 247 then
(if i.val < 246 then
0
else
0)
else
(if i.val < 248 then
0
else
0)))
else
(if i.val < 253 then
(if i.val < 251 then
(if i.val < 250 then
0
else
0)
else
(if i.val < 252 then
0
else
0))
else
(if i.val < 255 then
(if i.val < 254 then
0
else
0)
else
(if i.val < 256 then
0
else
(if i.val < 257 then
0
else
0)))))
else
(if i.val < 267 then
(if i.val < 262 then
(if i.val < 260 then
(if i.val < 259 then
0
else
0)
else
(if i.val < 261 then
0
else
5))
else
(if i.val < 264 then
(if i.val < 263 then
0
else
0)
else
(if i.val < 265 then
0
else
(if i.val < 266 then
0
else
0))))
else
(if i.val < 271 then
(if i.val < 269 then
(if i.val < 268 then
0
else
0)
else
(if i.val < 270 then
0
else
0))
else
(if i.val < 273 then
(if i.val < 272 then
0
else
0)
else
(if i.val < 274 then
0
else
(if i.val < 275 then
0
else
0)))))))))
else
(if i.val < 414 then
(if i.val < 345 then
(if i.val < 310 then
(if i.val < 293 then
(if i.val < 284 then
(if i.val < 280 then
(if i.val < 278 then
(if i.val < 277 then
0
else
0)
else
(if i.val < 279 then
0
else
0))
else
(if i.val < 282 then
(if i.val < 281 then
0
else
0)
else
(if i.val < 283 then
0
else
0)))
else
(if i.val < 288 then
(if i.val < 286 then
(if i.val < 285 then
0
else
0)
else
(if i.val < 287 then
0
else
0))
else
(if i.val < 290 then
(if i.val < 289 then
0
else
0)
else
(if i.val < 291 then
0
else
(if i.val < 292 then
0
else
0)))))
else
(if i.val < 301 then
(if i.val < 297 then
(if i.val < 295 then
(if i.val < 294 then
0
else
0)
else
(if i.val < 296 then
12
else
0))
else
(if i.val < 299 then
(if i.val < 298 then
0
else
0)
else
(if i.val < 300 then
0
else
0)))
else
(if i.val < 305 then
(if i.val < 303 then
(if i.val < 302 then
0
else
0)
else
(if i.val < 304 then
12
else
0))
else
(if i.val < 307 then
(if i.val < 306 then
0
else
0)
else
(if i.val < 308 then
0
else
(if i.val < 309 then
0
else
0))))))
else
(if i.val < 327 then
(if i.val < 318 then
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
0
else
0)
else
(if i.val < 313 then
0
else
0))
else
(if i.val < 316 then
(if i.val < 315 then
0
else
0)
else
(if i.val < 317 then
0
else
0)))
else
(if i.val < 322 then
(if i.val < 320 then
(if i.val < 319 then
0
else
0)
else
(if i.val < 321 then
0
else
0))
else
(if i.val < 324 then
(if i.val < 323 then
0
else
0)
else
(if i.val < 325 then
0
else
(if i.val < 326 then
0
else
0)))))
else
(if i.val < 336 then
(if i.val < 331 then
(if i.val < 329 then
(if i.val < 328 then
0
else
0)
else
(if i.val < 330 then
0
else
0))
else
(if i.val < 333 then
(if i.val < 332 then
0
else
0)
else
(if i.val < 334 then
0
else
(if i.val < 335 then
0
else
0))))
else
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
(if i.val < 344 then
0
else
0)))))))
else
(if i.val < 379 then
(if i.val < 362 then
(if i.val < 353 then
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
0
else
0)
else
(if i.val < 348 then
5
else
0))
else
(if i.val < 351 then
(if i.val < 350 then
0
else
0)
else
(if i.val < 352 then
0
else
0)))
else
(if i.val < 357 then
(if i.val < 355 then
(if i.val < 354 then
0
else
0)
else
(if i.val < 356 then
0
else
0))
else
(if i.val < 359 then
(if i.val < 358 then
5
else
0)
else
(if i.val < 360 then
0
else
(if i.val < 361 then
0
else
0)))))
else
(if i.val < 370 then
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
0
else
0)
else
(if i.val < 365 then
0
else
0))
else
(if i.val < 368 then
(if i.val < 367 then
0
else
0)
else
(if i.val < 369 then
0
else
0)))
else
(if i.val < 374 then
(if i.val < 372 then
(if i.val < 371 then
12
else
0)
else
(if i.val < 373 then
0
else
0))
else
(if i.val < 376 then
(if i.val < 375 then
0
else
0)
else
(if i.val < 377 then
0
else
(if i.val < 378 then
0
else
0))))))
else
(if i.val < 396 then
(if i.val < 387 then
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
0
else
0)
else
(if i.val < 382 then
0
else
0))
else
(if i.val < 385 then
(if i.val < 384 then
0
else
0)
else
(if i.val < 386 then
0
else
0)))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
0
else
0)
else
(if i.val < 390 then
0
else
0))
else
(if i.val < 393 then
(if i.val < 392 then
0
else
0)
else
(if i.val < 394 then
0
else
(if i.val < 395 then
0
else
0)))))
else
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
0
else
0)
else
(if i.val < 399 then
0
else
0))
else
(if i.val < 402 then
(if i.val < 401 then
0
else
0)
else
(if i.val < 403 then
0
else
(if i.val < 404 then
0
else
0))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
0
else
0)
else
(if i.val < 408 then
0
else
0))
else
(if i.val < 411 then
(if i.val < 410 then
0
else
0)
else
(if i.val < 412 then
0
else
(if i.val < 413 then
0
else
0))))))))
else
(if i.val < 483 then
(if i.val < 448 then
(if i.val < 431 then
(if i.val < 422 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
0
else
0)
else
(if i.val < 417 then
0
else
0))
else
(if i.val < 420 then
(if i.val < 419 then
0
else
0)
else
(if i.val < 421 then
0
else
0)))
else
(if i.val < 426 then
(if i.val < 424 then
(if i.val < 423 then
0
else
0)
else
(if i.val < 425 then
0
else
0))
else
(if i.val < 428 then
(if i.val < 427 then
0
else
0)
else
(if i.val < 429 then
0
else
(if i.val < 430 then
0
else
0)))))
else
(if i.val < 439 then
(if i.val < 435 then
(if i.val < 433 then
(if i.val < 432 then
0
else
0)
else
(if i.val < 434 then
12
else
0))
else
(if i.val < 437 then
(if i.val < 436 then
0
else
0)
else
(if i.val < 438 then
0
else
0)))
else
(if i.val < 443 then
(if i.val < 441 then
(if i.val < 440 then
0
else
0)
else
(if i.val < 442 then
5
else
0))
else
(if i.val < 445 then
(if i.val < 444 then
0
else
0)
else
(if i.val < 446 then
0
else
(if i.val < 447 then
0
else
0))))))
else
(if i.val < 465 then
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
12)
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
12))
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
(if i.val < 464 then
0
else
0)))))
else
(if i.val < 474 then
(if i.val < 469 then
(if i.val < 467 then
(if i.val < 466 then
0
else
0)
else
(if i.val < 468 then
0
else
0))
else
(if i.val < 471 then
(if i.val < 470 then
0
else
0)
else
(if i.val < 472 then
0
else
(if i.val < 473 then
0
else
12))))
else
(if i.val < 478 then
(if i.val < 476 then
(if i.val < 475 then
0
else
0)
else
(if i.val < 477 then
0
else
0))
else
(if i.val < 480 then
(if i.val < 479 then
0
else
0)
else
(if i.val < 481 then
0
else
(if i.val < 482 then
0
else
0)))))))
else
(if i.val < 517 then
(if i.val < 500 then
(if i.val < 491 then
(if i.val < 487 then
(if i.val < 485 then
(if i.val < 484 then
5
else
0)
else
(if i.val < 486 then
5
else
0))
else
(if i.val < 489 then
(if i.val < 488 then
5
else
0)
else
(if i.val < 490 then
0
else
0)))
else
(if i.val < 495 then
(if i.val < 493 then
(if i.val < 492 then
0
else
0)
else
(if i.val < 494 then
12
else
0))
else
(if i.val < 497 then
(if i.val < 496 then
0
else
0)
else
(if i.val < 498 then
0
else
(if i.val < 499 then
0
else
0)))))
else
(if i.val < 508 then
(if i.val < 504 then
(if i.val < 502 then
(if i.val < 501 then
0
else
0)
else
(if i.val < 503 then
0
else
0))
else
(if i.val < 506 then
(if i.val < 505 then
0
else
0)
else
(if i.val < 507 then
0
else
0)))
else
(if i.val < 512 then
(if i.val < 510 then
(if i.val < 509 then
0
else
0)
else
(if i.val < 511 then
0
else
0))
else
(if i.val < 514 then
(if i.val < 513 then
0
else
0)
else
(if i.val < 515 then
0
else
(if i.val < 516 then
0
else
0))))))
else
(if i.val < 534 then
(if i.val < 525 then
(if i.val < 521 then
(if i.val < 519 then
(if i.val < 518 then
0
else
0)
else
(if i.val < 520 then
0
else
0))
else
(if i.val < 523 then
(if i.val < 522 then
0
else
0)
else
(if i.val < 524 then
0
else
0)))
else
(if i.val < 529 then
(if i.val < 527 then
(if i.val < 526 then
0
else
0)
else
(if i.val < 528 then
12
else
0))
else
(if i.val < 531 then
(if i.val < 530 then
0
else
0)
else
(if i.val < 532 then
0
else
(if i.val < 533 then
0
else
0)))))
else
(if i.val < 543 then
(if i.val < 538 then
(if i.val < 536 then
(if i.val < 535 then
0
else
0)
else
(if i.val < 537 then
0
else
0))
else
(if i.val < 540 then
(if i.val < 539 then
0
else
0)
else
(if i.val < 541 then
0
else
(if i.val < 542 then
5
else
0))))
else
(if i.val < 547 then
(if i.val < 545 then
(if i.val < 544 then
0
else
0)
else
(if i.val < 546 then
0
else
0))
else
(if i.val < 549 then
(if i.val < 548 then
0
else
5)
else
(if i.val < 550 then
0
else
(if i.val < 551 then
0
else
0))))))))))

def g32p_row06_cosetExponents2 : Fin 552 → Multiplicative (ZMod 6) :=
  fun i => (if i.val < 276 then
(if i.val < 138 then
(if i.val < 69 then
(if i.val < 34 then
(if i.val < 17 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 3 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 6 then
(if i.val < 5 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 7 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 11 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 14 then
(if i.val < 13 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 15 then
Multiplicative.ofAdd 0
else
(if i.val < 16 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 25 then
(if i.val < 21 then
(if i.val < 19 then
(if i.val < 18 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 20 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 23 then
(if i.val < 22 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 24 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 29 then
(if i.val < 27 then
(if i.val < 26 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 28 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 31 then
(if i.val < 30 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 32 then
Multiplicative.ofAdd 0
else
(if i.val < 33 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 51 then
(if i.val < 42 then
(if i.val < 38 then
(if i.val < 36 then
(if i.val < 35 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 37 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 40 then
(if i.val < 39 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 41 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 46 then
(if i.val < 44 then
(if i.val < 43 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 45 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 48 then
(if i.val < 47 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 49 then
Multiplicative.ofAdd 0
else
(if i.val < 50 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 60 then
(if i.val < 55 then
(if i.val < 53 then
(if i.val < 52 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 54 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 57 then
(if i.val < 56 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 58 then
Multiplicative.ofAdd 0
else
(if i.val < 59 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 64 then
(if i.val < 62 then
(if i.val < 61 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 63 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 66 then
(if i.val < 65 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 67 then
Multiplicative.ofAdd 0
else
(if i.val < 68 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))
else
(if i.val < 103 then
(if i.val < 86 then
(if i.val < 77 then
(if i.val < 73 then
(if i.val < 71 then
(if i.val < 70 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 72 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 75 then
(if i.val < 74 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 76 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 81 then
(if i.val < 79 then
(if i.val < 78 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 80 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 83 then
(if i.val < 82 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 84 then
Multiplicative.ofAdd 0
else
(if i.val < 85 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 94 then
(if i.val < 90 then
(if i.val < 88 then
(if i.val < 87 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 89 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 92 then
(if i.val < 91 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 93 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 98 then
(if i.val < 96 then
(if i.val < 95 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 97 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 100 then
(if i.val < 99 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 101 then
Multiplicative.ofAdd 0
else
(if i.val < 102 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 120 then
(if i.val < 111 then
(if i.val < 107 then
(if i.val < 105 then
(if i.val < 104 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 106 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 109 then
(if i.val < 108 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 110 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 115 then
(if i.val < 113 then
(if i.val < 112 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 114 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 117 then
(if i.val < 116 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 118 then
Multiplicative.ofAdd 0
else
(if i.val < 119 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 129 then
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 123 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 126 then
(if i.val < 125 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 127 then
Multiplicative.ofAdd 0
else
(if i.val < 128 then
Multiplicative.ofAdd 3
else
Multiplicative.ofAdd 0))))
else
(if i.val < 133 then
(if i.val < 131 then
(if i.val < 130 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 132 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 135 then
(if i.val < 134 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 136 then
Multiplicative.ofAdd 0
else
(if i.val < 137 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))))
else
(if i.val < 207 then
(if i.val < 172 then
(if i.val < 155 then
(if i.val < 146 then
(if i.val < 142 then
(if i.val < 140 then
(if i.val < 139 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 141 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 144 then
(if i.val < 143 then
Multiplicative.ofAdd 3
else
Multiplicative.ofAdd 0)
else
(if i.val < 145 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 150 then
(if i.val < 148 then
(if i.val < 147 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 149 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 152 then
(if i.val < 151 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 153 then
Multiplicative.ofAdd 0
else
(if i.val < 154 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 163 then
(if i.val < 159 then
(if i.val < 157 then
(if i.val < 156 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 158 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 161 then
(if i.val < 160 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 162 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 167 then
(if i.val < 165 then
(if i.val < 164 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 166 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 169 then
(if i.val < 168 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 170 then
Multiplicative.ofAdd 0
else
(if i.val < 171 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 189 then
(if i.val < 180 then
(if i.val < 176 then
(if i.val < 174 then
(if i.val < 173 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 175 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 178 then
(if i.val < 177 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 179 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 184 then
(if i.val < 182 then
(if i.val < 181 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 183 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 186 then
(if i.val < 185 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 187 then
Multiplicative.ofAdd 0
else
(if i.val < 188 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 198 then
(if i.val < 193 then
(if i.val < 191 then
(if i.val < 190 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 192 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 195 then
(if i.val < 194 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 196 then
Multiplicative.ofAdd 0
else
(if i.val < 197 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 202 then
(if i.val < 200 then
(if i.val < 199 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 201 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 204 then
(if i.val < 203 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 205 then
Multiplicative.ofAdd 0
else
(if i.val < 206 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 3)))))))
else
(if i.val < 241 then
(if i.val < 224 then
(if i.val < 215 then
(if i.val < 211 then
(if i.val < 209 then
(if i.val < 208 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 210 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 213 then
(if i.val < 212 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 214 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 219 then
(if i.val < 217 then
(if i.val < 216 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 218 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 221 then
(if i.val < 220 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 222 then
Multiplicative.ofAdd 0
else
(if i.val < 223 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 227 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 230 then
(if i.val < 229 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 231 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 235 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 238 then
(if i.val < 237 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 239 then
Multiplicative.ofAdd 0
else
(if i.val < 240 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 258 then
(if i.val < 249 then
(if i.val < 245 then
(if i.val < 243 then
(if i.val < 242 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 244 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 247 then
(if i.val < 246 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 248 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 253 then
(if i.val < 251 then
(if i.val < 250 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 252 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 255 then
(if i.val < 254 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 256 then
Multiplicative.ofAdd 0
else
(if i.val < 257 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 267 then
(if i.val < 262 then
(if i.val < 260 then
(if i.val < 259 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 261 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 3))
else
(if i.val < 264 then
(if i.val < 263 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 265 then
Multiplicative.ofAdd 0
else
(if i.val < 266 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 271 then
(if i.val < 269 then
(if i.val < 268 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 270 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 273 then
(if i.val < 272 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 274 then
Multiplicative.ofAdd 0
else
(if i.val < 275 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))))
else
(if i.val < 414 then
(if i.val < 345 then
(if i.val < 310 then
(if i.val < 293 then
(if i.val < 284 then
(if i.val < 280 then
(if i.val < 278 then
(if i.val < 277 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 279 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 282 then
(if i.val < 281 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 283 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 288 then
(if i.val < 286 then
(if i.val < 285 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 287 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 290 then
(if i.val < 289 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 291 then
Multiplicative.ofAdd 0
else
(if i.val < 292 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 301 then
(if i.val < 297 then
(if i.val < 295 then
(if i.val < 294 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 296 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 299 then
(if i.val < 298 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 300 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 305 then
(if i.val < 303 then
(if i.val < 302 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 304 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 307 then
(if i.val < 306 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 308 then
Multiplicative.ofAdd 0
else
(if i.val < 309 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 327 then
(if i.val < 318 then
(if i.val < 314 then
(if i.val < 312 then
(if i.val < 311 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 313 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 316 then
(if i.val < 315 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 317 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 322 then
(if i.val < 320 then
(if i.val < 319 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 321 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 324 then
(if i.val < 323 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 325 then
Multiplicative.ofAdd 0
else
(if i.val < 326 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 336 then
(if i.val < 331 then
(if i.val < 329 then
(if i.val < 328 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 330 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 333 then
(if i.val < 332 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 334 then
Multiplicative.ofAdd 0
else
(if i.val < 335 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 339 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 342 then
(if i.val < 341 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 343 then
Multiplicative.ofAdd 0
else
(if i.val < 344 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))
else
(if i.val < 379 then
(if i.val < 362 then
(if i.val < 353 then
(if i.val < 349 then
(if i.val < 347 then
(if i.val < 346 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 348 then
Multiplicative.ofAdd 3
else
Multiplicative.ofAdd 0))
else
(if i.val < 351 then
(if i.val < 350 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 352 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 357 then
(if i.val < 355 then
(if i.val < 354 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 356 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 359 then
(if i.val < 358 then
Multiplicative.ofAdd 3
else
Multiplicative.ofAdd 0)
else
(if i.val < 360 then
Multiplicative.ofAdd 0
else
(if i.val < 361 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 370 then
(if i.val < 366 then
(if i.val < 364 then
(if i.val < 363 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 365 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 368 then
(if i.val < 367 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 369 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 374 then
(if i.val < 372 then
(if i.val < 371 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 373 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 376 then
(if i.val < 375 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 377 then
Multiplicative.ofAdd 0
else
(if i.val < 378 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 396 then
(if i.val < 387 then
(if i.val < 383 then
(if i.val < 381 then
(if i.val < 380 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 382 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 385 then
(if i.val < 384 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 386 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 391 then
(if i.val < 389 then
(if i.val < 388 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 390 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 393 then
(if i.val < 392 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 394 then
Multiplicative.ofAdd 0
else
(if i.val < 395 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 405 then
(if i.val < 400 then
(if i.val < 398 then
(if i.val < 397 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 399 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 402 then
(if i.val < 401 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 403 then
Multiplicative.ofAdd 0
else
(if i.val < 404 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 409 then
(if i.val < 407 then
(if i.val < 406 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 408 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 411 then
(if i.val < 410 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 412 then
Multiplicative.ofAdd 0
else
(if i.val < 413 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))))
else
(if i.val < 483 then
(if i.val < 448 then
(if i.val < 431 then
(if i.val < 422 then
(if i.val < 418 then
(if i.val < 416 then
(if i.val < 415 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 417 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 420 then
(if i.val < 419 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 421 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 426 then
(if i.val < 424 then
(if i.val < 423 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 425 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 428 then
(if i.val < 427 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 429 then
Multiplicative.ofAdd 0
else
(if i.val < 430 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 439 then
(if i.val < 435 then
(if i.val < 433 then
(if i.val < 432 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 434 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 437 then
(if i.val < 436 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 438 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 443 then
(if i.val < 441 then
(if i.val < 440 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 442 then
Multiplicative.ofAdd 3
else
Multiplicative.ofAdd 0))
else
(if i.val < 445 then
(if i.val < 444 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 446 then
Multiplicative.ofAdd 0
else
(if i.val < 447 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 465 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 451 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 454 then
(if i.val < 453 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 455 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 459 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 462 then
(if i.val < 461 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 463 then
Multiplicative.ofAdd 0
else
(if i.val < 464 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 474 then
(if i.val < 469 then
(if i.val < 467 then
(if i.val < 466 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 468 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 471 then
(if i.val < 470 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 472 then
Multiplicative.ofAdd 0
else
(if i.val < 473 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))
else
(if i.val < 478 then
(if i.val < 476 then
(if i.val < 475 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 477 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 480 then
(if i.val < 479 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 481 then
Multiplicative.ofAdd 0
else
(if i.val < 482 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))))
else
(if i.val < 517 then
(if i.val < 500 then
(if i.val < 491 then
(if i.val < 487 then
(if i.val < 485 then
(if i.val < 484 then
Multiplicative.ofAdd 3
else
Multiplicative.ofAdd 0)
else
(if i.val < 486 then
Multiplicative.ofAdd 3
else
Multiplicative.ofAdd 0))
else
(if i.val < 489 then
(if i.val < 488 then
Multiplicative.ofAdd 3
else
Multiplicative.ofAdd 0)
else
(if i.val < 490 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 495 then
(if i.val < 493 then
(if i.val < 492 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 494 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 497 then
(if i.val < 496 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 498 then
Multiplicative.ofAdd 0
else
(if i.val < 499 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 508 then
(if i.val < 504 then
(if i.val < 502 then
(if i.val < 501 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 503 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 506 then
(if i.val < 505 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 507 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 512 then
(if i.val < 510 then
(if i.val < 509 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 511 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 514 then
(if i.val < 513 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 515 then
Multiplicative.ofAdd 0
else
(if i.val < 516 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))
else
(if i.val < 534 then
(if i.val < 525 then
(if i.val < 521 then
(if i.val < 519 then
(if i.val < 518 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 520 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 523 then
(if i.val < 522 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 524 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))
else
(if i.val < 529 then
(if i.val < 527 then
(if i.val < 526 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 528 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 531 then
(if i.val < 530 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 532 then
Multiplicative.ofAdd 0
else
(if i.val < 533 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)))))
else
(if i.val < 543 then
(if i.val < 538 then
(if i.val < 536 then
(if i.val < 535 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 537 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 540 then
(if i.val < 539 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 541 then
Multiplicative.ofAdd 0
else
(if i.val < 542 then
Multiplicative.ofAdd 3
else
Multiplicative.ofAdd 0))))
else
(if i.val < 547 then
(if i.val < 545 then
(if i.val < 544 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0)
else
(if i.val < 546 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))
else
(if i.val < 549 then
(if i.val < 548 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 3)
else
(if i.val < 550 then
Multiplicative.ofAdd 0
else
(if i.val < 551 then
Multiplicative.ofAdd 0
else
Multiplicative.ofAdd 0))))))))))


end HodgeLean.Foundations.Program
