# G32 release kernel replay manifest

Note: Shards 31 and 32 ran twice: the first attempts (2 CPU, 64 GB) lost their containers, likely out of memory, with no REPLAY-FAIL line; their partial progress files are kept in state/replay-evidence/. The second attempts (128 GB, same commit and --shard bounds) are the ones counted.

Note: Shard 11 (checked modules 10694..11376) was re-run as sub-ranges with the same commit, roots and tool: kreplay-rel2-11s-00..39 except 10 and 11, plus kreplay-rel2-11t-00..23 covering 11169..11264 in 4-module chunks. Each sub-range uses leanchecker range semantics: modules before the range start are loaded from compiled files with the trusted base, and only the range is replayed. The original single-container shard 11 replayed 570 of its 682 modules with matching counts before this manifest; it is not counted here.

- commit: 0ea348972dc8396faee9eef1caa89f9d5908823f
- source tree hash (sha256 of sha256s of *.lean, lakefile, manifest, toolchain): e334b58f9508c9156c3ba31e0531aa30301de9bab0c0de3657276d713983c9de
- olean set sha256 (HodgeLean project, before replay): 9e7f20c822dc356ec17eecc615c127c776e78ac95686ce170186b761b0b1ba91
- tool: ReplayClosure.lean sha256 7b433f431179ad6ff00a485c832fb433080b5272d47ca73224f54c9bacd5de0b
- shards: 101 of 101 PASS; checked modules covered: 13315 of 13315; constants replayed: 1065796
- negative control (kreplay-rel2-control): rejected as required
- longest shard: 112.0 min; summed shard time: 38.1 h

| shard | range | modules | constants | minutes |
|---|---|---|---|---|
| kreplay-rel2-00 | 0..664 | 664 | 17917 | 69.6 |
| kreplay-rel2-01 | 664..1013 | 349 | 8747 | 79.9 |
| kreplay-rel2-02 | 1013..1362 | 349 | 8695 | 66.5 |
| kreplay-rel2-03 | 1362..1737 | 375 | 10377 | 3.3 |
| kreplay-rel2-04 | 1737..2228 | 491 | 9316 | 14.9 |
| kreplay-rel2-05 | 2228..2864 | 636 | 9028 | 34.0 |
| kreplay-rel2-06 | 2864..4357 | 1493 | 7854 | 9.6 |
| kreplay-rel2-07 | 4357..5955 | 1598 | 7798 | 5.8 |
| kreplay-rel2-08 | 5955..7184 | 1229 | 5773 | 13.7 |
| kreplay-rel2-09 | 7184..9023 | 1839 | 14424 | 23.6 |
| kreplay-rel2-10 | 9023..10694 | 1671 | 9321 | 48.0 |
| kreplay-rel2-11s-00 | 10694..10741 | 47 | 128 | 1.0 |
| kreplay-rel2-11s-01 | 10741..10789 | 48 | 147 | 1.9 |
| kreplay-rel2-11s-02 | 10789..10836 | 47 | 171 | 3.8 |
| kreplay-rel2-11s-03 | 10836..10884 | 48 | 115 | 5.0 |
| kreplay-rel2-11s-04 | 10884..10931 | 47 | 237 | 4.5 |
| kreplay-rel2-11s-05 | 10931..10979 | 48 | 1499 | 11.3 |
| kreplay-rel2-11s-06 | 10979..11026 | 47 | 1930 | 1.4 |
| kreplay-rel2-11s-07 | 11026..11074 | 48 | 530 | 1.1 |
| kreplay-rel2-11s-08 | 11074..11121 | 47 | 900 | 1.7 |
| kreplay-rel2-11s-09 | 11121..11169 | 48 | 886 | 25.1 |
| kreplay-rel2-11t-00 | 11169..11173 | 4 | 192 | 10.3 |
| kreplay-rel2-11t-01 | 11173..11177 | 4 | 156 | 9.8 |
| kreplay-rel2-11t-02 | 11177..11181 | 4 | 48 | 6.0 |
| kreplay-rel2-11t-03 | 11181..11185 | 4 | 48 | 5.2 |
| kreplay-rel2-11t-04 | 11185..11189 | 4 | 48 | 5.1 |
| kreplay-rel2-11t-05 | 11189..11193 | 4 | 48 | 6.4 |
| kreplay-rel2-11t-06 | 11193..11197 | 4 | 48 | 5.8 |
| kreplay-rel2-11t-07 | 11197..11201 | 4 | 48 | 6.9 |
| kreplay-rel2-11t-08 | 11201..11205 | 4 | 48 | 7.3 |
| kreplay-rel2-11t-09 | 11205..11209 | 4 | 48 | 7.2 |
| kreplay-rel2-11t-10 | 11209..11213 | 4 | 48 | 10.3 |
| kreplay-rel2-11t-11 | 11213..11217 | 4 | 48 | 10.4 |
| kreplay-rel2-11t-12 | 11217..11221 | 4 | 48 | 9.4 |
| kreplay-rel2-11t-13 | 11221..11225 | 4 | 48 | 8.5 |
| kreplay-rel2-11t-14 | 11225..11229 | 4 | 48 | 9.7 |
| kreplay-rel2-11t-15 | 11229..11233 | 4 | 48 | 8.6 |
| kreplay-rel2-11t-16 | 11233..11237 | 4 | 48 | 8.0 |
| kreplay-rel2-11t-17 | 11237..11241 | 4 | 48 | 11.1 |
| kreplay-rel2-11t-18 | 11241..11245 | 4 | 48 | 13.7 |
| kreplay-rel2-11t-19 | 11245..11249 | 4 | 48 | 16.8 |
| kreplay-rel2-11t-20 | 11249..11253 | 4 | 48 | 16.7 |
| kreplay-rel2-11t-21 | 11253..11257 | 4 | 48 | 14.1 |
| kreplay-rel2-11t-22 | 11257..11261 | 4 | 48 | 15.8 |
| kreplay-rel2-11t-23 | 11261..11264 | 3 | 36 | 10.4 |
| kreplay-rel2-11s-12 | 11264..11268 | 4 | 48 | 23.9 |
| kreplay-rel2-11s-13 | 11268..11272 | 4 | 48 | 14.3 |
| kreplay-rel2-11s-14 | 11272..11276 | 4 | 48 | 20.5 |
| kreplay-rel2-11s-15 | 11276..11280 | 4 | 48 | 26.5 |
| kreplay-rel2-11s-16 | 11280..11284 | 4 | 48 | 19.6 |
| kreplay-rel2-11s-17 | 11284..11288 | 4 | 48 | 21.3 |
| kreplay-rel2-11s-18 | 11288..11292 | 4 | 48 | 22.6 |
| kreplay-rel2-11s-19 | 11292..11296 | 4 | 48 | 21.5 |
| kreplay-rel2-11s-20 | 11296..11300 | 4 | 48 | 20.9 |
| kreplay-rel2-11s-21 | 11300..11304 | 4 | 48 | 23.1 |
| kreplay-rel2-11s-22 | 11304..11308 | 4 | 48 | 28.5 |
| kreplay-rel2-11s-23 | 11308..11312 | 4 | 48 | 27.1 |
| kreplay-rel2-11s-24 | 11312..11316 | 4 | 48 | 29.9 |
| kreplay-rel2-11s-25 | 11316..11320 | 4 | 48 | 30.2 |
| kreplay-rel2-11s-26 | 11320..11324 | 4 | 48 | 29.0 |
| kreplay-rel2-11s-27 | 11324..11328 | 4 | 48 | 24.6 |
| kreplay-rel2-11s-28 | 11328..11332 | 4 | 48 | 29.7 |
| kreplay-rel2-11s-29 | 11332..11336 | 4 | 48 | 30.9 |
| kreplay-rel2-11s-30 | 11336..11340 | 4 | 153 | 2.3 |
| kreplay-rel2-11s-31 | 11340..11344 | 4 | 126 | 2.6 |
| kreplay-rel2-11s-32 | 11344..11348 | 4 | 128 | 2.9 |
| kreplay-rel2-11s-33 | 11348..11352 | 4 | 128 | 2.7 |
| kreplay-rel2-11s-34 | 11352..11356 | 4 | 128 | 3.5 |
| kreplay-rel2-11s-35 | 11356..11360 | 4 | 126 | 6.4 |
| kreplay-rel2-11s-36 | 11360..11364 | 4 | 36 | 1.1 |
| kreplay-rel2-11s-37 | 11364..11368 | 4 | 61 | 0.8 |
| kreplay-rel2-11s-38 | 11368..11372 | 4 | 19 | 1.1 |
| kreplay-rel2-11s-39 | 11372..11376 | 4 | 117 | 1.0 |
| kreplay-rel2-12 | 11376..11502 | 126 | 3062 | 103.6 |
| kreplay-rel2-13 | 11502..11519 | 17 | 1232 | 2.7 |
| kreplay-rel2-14 | 11519..11532 | 13 | 1255 | 2.5 |
| kreplay-rel2-15 | 11532..11547 | 15 | 1050 | 2.3 |
| kreplay-rel2-16 | 11547..11558 | 11 | 1123 | 2.4 |
| kreplay-rel2-17 | 11558..11606 | 48 | 1636 | 3.0 |
| kreplay-rel2-18 | 11606..11705 | 99 | 2779 | 23.4 |
| kreplay-rel2-19 | 11705..11758 | 53 | 8373 | 18.8 |
| kreplay-rel2-20 | 11758..11809 | 51 | 7196 | 36.0 |
| kreplay-rel2-21 | 11809..11888 | 79 | 13307 | 112.0 |
| kreplay-rel2-22 | 11888..11924 | 36 | 65541 | 13.3 |
| kreplay-rel2-23 | 11924..11958 | 34 | 62639 | 17.3 |
| kreplay-rel2-24 | 11958..12008 | 50 | 164217 | 24.6 |
| kreplay-rel2-25 | 12008..12082 | 74 | 176789 | 26.4 |
| kreplay-rel2-26 | 12082..12158 | 76 | 96303 | 81.9 |
| kreplay-rel2-27 | 12158..12235 | 77 | 22355 | 66.8 |
| kreplay-rel2-28 | 12235..12295 | 60 | 23021 | 48.1 |
| kreplay-rel2-29 | 12295..12321 | 26 | 24124 | 43.3 |
| kreplay-rel2-30 | 12321..12356 | 35 | 13873 | 25.3 |
| kreplay-rel2-31 | 12356..12413 | 57 | 43236 | 93.3 |
| kreplay-rel2-32 | 12413..12460 | 47 | 23840 | 59.2 |
| kreplay-rel2-33 | 12460..12525 | 65 | 25553 | 52.1 |
| kreplay-rel2-34 | 12525..12541 | 16 | 4609 | 7.9 |
| kreplay-rel2-35 | 12541..12577 | 36 | 39958 | 78.6 |
| kreplay-rel2-36 | 12577..12649 | 72 | 47892 | 81.2 |
| kreplay-rel2-37 | 12649..12695 | 46 | 22101 | 34.3 |
| kreplay-rel2-38 | 12695..12744 | 49 | 32987 | 59.7 |
| kreplay-rel2-39 | 12744..13315 | 571 | 16674 | 36.4 |

RESULT: PASS (all shards pass, ranges tile the closure, hashes agree, control rejected)
