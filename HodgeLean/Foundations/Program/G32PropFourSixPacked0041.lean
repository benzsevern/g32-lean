import HodgeLean.Foundations.Program.G32PropFourSixPacked0037
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow03Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0039
import HodgeLean.Foundations.Program.G32PropFourSixPacked0040
import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_groupTransition :
    g32p_transitionCheck g32p_row03_groupNodes g32p_row03_groupMatrices
      g32p_row03_groupNext = true := by
  apply g32p_transition_integral_check_of_steps
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row03_transitionBlock_000
  · exact g32p_row03_transitionBlock_001
  · exact g32p_row03_transitionBlock_002
  · exact g32p_row03_transitionBlock_003
  · exact g32p_row03_transitionBlock_004
  · exact g32p_row03_transitionBlock_005
  · exact g32p_row03_transitionBlock_006
  · exact g32p_row03_transitionBlock_007
  · exact g32p_row03_transitionBlock_008
  · exact g32p_row03_transitionBlock_009
  · exact g32p_row03_transitionBlock_010
  · exact g32p_row03_transitionBlock_011
  · exact g32p_row03_transitionBlock_012
  · exact g32p_row03_transitionBlock_013
  · exact g32p_row03_transitionBlock_014
  · exact g32p_row03_transitionBlock_015
  · exact g32p_row03_transitionBlock_016
  · exact g32p_row03_transitionBlock_017
  · exact g32p_row03_transitionBlock_018
  · exact g32p_row03_transitionBlock_019
  · exact g32p_row03_transitionBlock_020
  · exact g32p_row03_transitionBlock_021
  · exact g32p_row03_transitionBlock_022
  · exact g32p_row03_transitionBlock_023
  · exact g32p_row03_transitionBlock_024
  · exact g32p_row03_transitionBlock_025
  · exact g32p_row03_transitionBlock_026
  · exact g32p_row03_transitionBlock_027
  · exact g32p_row03_transitionBlock_028
  · exact g32p_row03_transitionBlock_029
  · exact g32p_row03_transitionBlock_030
  · exact g32p_row03_transitionBlock_031
  · exact g32p_row03_transitionBlock_032
  · exact g32p_row03_transitionBlock_033
  · exact g32p_row03_transitionBlock_034
  · exact g32p_row03_transitionBlock_035
  · exact g32p_row03_transitionBlock_036
  · exact g32p_row03_transitionBlock_037
  · exact g32p_row03_transitionBlock_038
  · exact g32p_row03_transitionBlock_039
  · exact g32p_row03_transitionBlock_040
  · exact g32p_row03_transitionBlock_041
  · exact g32p_row03_transitionBlock_042
  · exact g32p_row03_transitionBlock_043
  · exact g32p_row03_transitionBlock_044
  · exact g32p_row03_transitionBlock_045
  · exact g32p_row03_transitionBlock_046
  · exact g32p_row03_transitionBlock_047
  · exact g32p_row03_transitionBlock_048
  · exact g32p_row03_transitionBlock_049
  · exact g32p_row03_transitionBlock_050
  · exact g32p_row03_transitionBlock_051
  · exact g32p_row03_transitionBlock_052
  · exact g32p_row03_transitionBlock_053
  · exact g32p_row03_transitionBlock_054
  · exact g32p_row03_transitionBlock_055
  · exact g32p_row03_transitionBlock_056
  · exact g32p_row03_transitionBlock_057
  · exact g32p_row03_transitionBlock_058
  · exact g32p_row03_transitionBlock_059
  · exact g32p_row03_transitionBlock_060
  · exact g32p_row03_transitionBlock_061
  · exact g32p_row03_transitionBlock_062
  · exact g32p_row03_transitionBlock_063
  · exact g32p_row03_transitionBlock_064
  · exact g32p_row03_transitionBlock_065
  · exact g32p_row03_transitionBlock_066
  · exact g32p_row03_transitionBlock_067
  · exact g32p_row03_transitionBlock_068
  · exact g32p_row03_transitionBlock_069
  · exact g32p_row03_transitionBlock_070
  · exact g32p_row03_transitionBlock_071
  · exact g32p_row03_transitionBlock_072
  · exact g32p_row03_transitionBlock_073
  · exact g32p_row03_transitionBlock_074
  · exact g32p_row03_transitionBlock_075
  · exact g32p_row03_transitionBlock_076
  · exact g32p_row03_transitionBlock_077
  · exact g32p_row03_transitionBlock_078
  · exact g32p_row03_transitionBlock_079
  · exact g32p_row03_transitionBlock_080
  · exact g32p_row03_transitionBlock_081
  · exact g32p_row03_transitionBlock_082
  · exact g32p_row03_transitionBlock_083
  · exact g32p_row03_transitionBlock_084
  · exact g32p_row03_transitionBlock_085
  · exact g32p_row03_transitionBlock_086
  · exact g32p_row03_transitionBlock_087
  · exact g32p_row03_transitionBlock_088
  · exact g32p_row03_transitionBlock_089
  · exact g32p_row03_transitionBlock_090
  · exact g32p_row03_transitionBlock_091
  · exact g32p_row03_transitionBlock_092
  · exact g32p_row03_transitionBlock_093
  · exact g32p_row03_transitionBlock_094
  · exact g32p_row03_transitionBlock_095
  · exact g32p_row03_transitionBlock_096
  · exact g32p_row03_transitionBlock_097
  · exact g32p_row03_transitionBlock_098
  · exact g32p_row03_transitionBlock_099
  · exact g32p_row03_transitionBlock_100
  · exact g32p_row03_transitionBlock_101
  · exact g32p_row03_transitionBlock_102
  · exact g32p_row03_transitionBlock_103
  · exact g32p_row03_transitionBlock_104
  · exact g32p_row03_transitionBlock_105
  · exact g32p_row03_transitionBlock_106
  · exact g32p_row03_transitionBlock_107
  · exact g32p_row03_transitionBlock_108
  · exact g32p_row03_transitionBlock_109
  · exact g32p_row03_transitionBlock_110
  · exact g32p_row03_transitionBlock_111
  · exact g32p_row03_transitionBlock_112
  · exact g32p_row03_transitionBlock_113
  · exact g32p_row03_transitionBlock_114
  · exact g32p_row03_transitionBlock_115
  · exact g32p_row03_transitionBlock_116
  · exact g32p_row03_transitionBlock_117
  · exact g32p_row03_transitionBlock_118
  · exact g32p_row03_transitionBlock_119
  · exact g32p_row03_transitionBlock_120
  · exact g32p_row03_transitionBlock_121
  · exact g32p_row03_transitionBlock_122
  · exact g32p_row03_transitionBlock_123
  · exact g32p_row03_transitionBlock_124
  · exact g32p_row03_transitionBlock_125
  · exact g32p_row03_transitionBlock_126
  · exact g32p_row03_transitionBlock_127
  · exact g32p_row03_transitionBlock_128
  · exact g32p_row03_transitionBlock_129
  · exact g32p_row03_transitionBlock_130
  · exact g32p_row03_transitionBlock_131
  · exact g32p_row03_transitionBlock_132
  · exact g32p_row03_transitionBlock_133
  · exact g32p_row03_transitionBlock_134
  · exact g32p_row03_transitionBlock_135
  · exact g32p_row03_transitionBlock_136
  · exact g32p_row03_transitionBlock_137
  · exact g32p_row03_transitionBlock_138
  · exact g32p_row03_transitionBlock_139
  · exact g32p_row03_transitionBlock_140
  · exact g32p_row03_transitionBlock_141
  · exact g32p_row03_transitionBlock_142
  · exact g32p_row03_transitionBlock_143
  · exact g32p_row03_transitionBlock_144
  · exact g32p_row03_transitionBlock_145
  · exact g32p_row03_transitionBlock_146
  · exact g32p_row03_transitionBlock_147
  · exact g32p_row03_transitionBlock_148
  · exact g32p_row03_transitionBlock_149
  · exact g32p_row03_transitionBlock_150
  · exact g32p_row03_transitionBlock_151
  · exact g32p_row03_transitionBlock_152
  · exact g32p_row03_transitionBlock_153
  · exact g32p_row03_transitionBlock_154
  · exact g32p_row03_transitionBlock_155
  · exact g32p_row03_transitionBlock_156
  · exact g32p_row03_transitionBlock_157
  · exact g32p_row03_transitionBlock_158
  · exact g32p_row03_transitionBlock_159
  · exact g32p_row03_transitionBlock_160
  · exact g32p_row03_transitionBlock_161
  · exact g32p_row03_transitionBlock_162
  · exact g32p_row03_transitionBlock_163
  · exact g32p_row03_transitionBlock_164
  · exact g32p_row03_transitionBlock_165
  · exact g32p_row03_transitionBlock_166
  · exact g32p_row03_transitionBlock_167
  · exact g32p_row03_transitionBlock_168
  · exact g32p_row03_transitionBlock_169
  · exact g32p_row03_transitionBlock_170
  · exact g32p_row03_transitionBlock_171
  · exact g32p_row03_transitionBlock_172
  · exact g32p_row03_transitionBlock_173
  · exact g32p_row03_transitionBlock_174
  · exact g32p_row03_transitionBlock_175
  · exact g32p_row03_transitionBlock_176
  · exact g32p_row03_transitionBlock_177
  · exact g32p_row03_transitionBlock_178
  · exact g32p_row03_transitionBlock_179
  · exact g32p_row03_transitionBlock_180
  · exact g32p_row03_transitionBlock_181
  · exact g32p_row03_transitionBlock_182
  · exact g32p_row03_transitionBlock_183
  · exact g32p_row03_transitionBlock_184
  · exact g32p_row03_transitionBlock_185
  · exact g32p_row03_transitionBlock_186
  · exact g32p_row03_transitionBlock_187
  · exact g32p_row03_transitionBlock_188
  · exact g32p_row03_transitionBlock_189
  · exact g32p_row03_transitionBlock_190
  · exact g32p_row03_transitionBlock_191
  · exact g32p_row03_transitionBlock_192
  · exact g32p_row03_transitionBlock_193
  · exact g32p_row03_transitionBlock_194
  · exact g32p_row03_transitionBlock_195
  · exact g32p_row03_transitionBlock_196
  · exact g32p_row03_transitionBlock_197
  · exact g32p_row03_transitionBlock_198
  · exact g32p_row03_transitionBlock_199
  · exact g32p_row03_transitionBlock_200
  · exact g32p_row03_transitionBlock_201
  · exact g32p_row03_transitionBlock_202
  · exact g32p_row03_transitionBlock_203
  · exact g32p_row03_transitionBlock_204
  · exact g32p_row03_transitionBlock_205
  · exact g32p_row03_transitionBlock_206
  · exact g32p_row03_transitionBlock_207
  · exact g32p_row03_transitionBlock_208
  · exact g32p_row03_transitionBlock_209
  · exact g32p_row03_transitionBlock_210
  · exact g32p_row03_transitionBlock_211
  · exact g32p_row03_transitionBlock_212
  · exact g32p_row03_transitionBlock_213
  · exact g32p_row03_transitionBlock_214
  · exact g32p_row03_transitionBlock_215
  · exact g32p_row03_transitionBlock_216
  · exact g32p_row03_transitionBlock_217
  · exact g32p_row03_transitionBlock_218
  · exact g32p_row03_transitionBlock_219
  · exact g32p_row03_transitionBlock_220
  · exact g32p_row03_transitionBlock_221
  · exact g32p_row03_transitionBlock_222
  · exact g32p_row03_transitionBlock_223
  · exact g32p_row03_transitionBlock_224
  · exact g32p_row03_transitionBlock_225
  · exact g32p_row03_transitionBlock_226
  · exact g32p_row03_transitionBlock_227
  · exact g32p_row03_transitionBlock_228
  · exact g32p_row03_transitionBlock_229
  · exact g32p_row03_transitionBlock_230
  · exact g32p_row03_transitionBlock_231
  · exact g32p_row03_transitionBlock_232
  · exact g32p_row03_transitionBlock_233
  · exact g32p_row03_transitionBlock_234
  · exact g32p_row03_transitionBlock_235
  · exact g32p_row03_transitionBlock_236
  · exact g32p_row03_transitionBlock_237
  · exact g32p_row03_transitionBlock_238
  · exact g32p_row03_transitionBlock_239
  · exact g32p_row03_transitionBlock_240
  · exact g32p_row03_transitionBlock_241
  · exact g32p_row03_transitionBlock_242
  · exact g32p_row03_transitionBlock_243
  · exact g32p_row03_transitionBlock_244
  · exact g32p_row03_transitionBlock_245
  · exact g32p_row03_transitionBlock_246
  · exact g32p_row03_transitionBlock_247
  · exact g32p_row03_transitionBlock_248
  · exact g32p_row03_transitionBlock_249
  · exact g32p_row03_transitionBlock_250
  · exact g32p_row03_transitionBlock_251
  · exact g32p_row03_transitionBlock_252
  · exact g32p_row03_transitionBlock_253
  · exact g32p_row03_transitionBlock_254
  · exact g32p_row03_transitionBlock_255
  · exact g32p_row03_transitionBlock_256
  · exact g32p_row03_transitionBlock_257
  · exact g32p_row03_transitionBlock_258
  · exact g32p_row03_transitionBlock_259
  · exact g32p_row03_transitionBlock_260
  · exact g32p_row03_transitionBlock_261
  · exact g32p_row03_transitionBlock_262
  · exact g32p_row03_transitionBlock_263
  · exact g32p_row03_transitionBlock_264
  · exact g32p_row03_transitionBlock_265
  · exact g32p_row03_transitionBlock_266
  · exact g32p_row03_transitionBlock_267
  · exact g32p_row03_transitionBlock_268
  · exact g32p_row03_transitionBlock_269

theorem g32p_row03_groupStep (i : Fin 4320) (s : Fin 2) :
    HurwitzPrymRex_mmul (g32p_row03_groupNodes i) (g32p_row03_groupMatrices s) =
      g32p_row03_groupNodes (g32p_row03_groupNext i s) := by
  exact g32p_transition_integral_sound _ _ _ g32p_row03_groupTransition i s


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_matrixDecode_leftInverse : ∀ i : Fin 4320,
    g32p_row03_matrixDecode (g32p_matrixFingerprint (g32p_row03_groupNodes i)) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row03_decodeBlock_000
  · exact g32p_row03_decodeBlock_001
  · exact g32p_row03_decodeBlock_002
  · exact g32p_row03_decodeBlock_003
  · exact g32p_row03_decodeBlock_004
  · exact g32p_row03_decodeBlock_005
  · exact g32p_row03_decodeBlock_006
  · exact g32p_row03_decodeBlock_007
  · exact g32p_row03_decodeBlock_008
  · exact g32p_row03_decodeBlock_009
  · exact g32p_row03_decodeBlock_010
  · exact g32p_row03_decodeBlock_011
  · exact g32p_row03_decodeBlock_012
  · exact g32p_row03_decodeBlock_013
  · exact g32p_row03_decodeBlock_014
  · exact g32p_row03_decodeBlock_015
  · exact g32p_row03_decodeBlock_016
  · exact g32p_row03_decodeBlock_017
  · exact g32p_row03_decodeBlock_018
  · exact g32p_row03_decodeBlock_019
  · exact g32p_row03_decodeBlock_020
  · exact g32p_row03_decodeBlock_021
  · exact g32p_row03_decodeBlock_022
  · exact g32p_row03_decodeBlock_023
  · exact g32p_row03_decodeBlock_024
  · exact g32p_row03_decodeBlock_025
  · exact g32p_row03_decodeBlock_026
  · exact g32p_row03_decodeBlock_027
  · exact g32p_row03_decodeBlock_028
  · exact g32p_row03_decodeBlock_029
  · exact g32p_row03_decodeBlock_030
  · exact g32p_row03_decodeBlock_031
  · exact g32p_row03_decodeBlock_032
  · exact g32p_row03_decodeBlock_033
  · exact g32p_row03_decodeBlock_034
  · exact g32p_row03_decodeBlock_035
  · exact g32p_row03_decodeBlock_036
  · exact g32p_row03_decodeBlock_037
  · exact g32p_row03_decodeBlock_038
  · exact g32p_row03_decodeBlock_039
  · exact g32p_row03_decodeBlock_040
  · exact g32p_row03_decodeBlock_041
  · exact g32p_row03_decodeBlock_042
  · exact g32p_row03_decodeBlock_043
  · exact g32p_row03_decodeBlock_044
  · exact g32p_row03_decodeBlock_045
  · exact g32p_row03_decodeBlock_046
  · exact g32p_row03_decodeBlock_047
  · exact g32p_row03_decodeBlock_048
  · exact g32p_row03_decodeBlock_049
  · exact g32p_row03_decodeBlock_050
  · exact g32p_row03_decodeBlock_051
  · exact g32p_row03_decodeBlock_052
  · exact g32p_row03_decodeBlock_053
  · exact g32p_row03_decodeBlock_054
  · exact g32p_row03_decodeBlock_055
  · exact g32p_row03_decodeBlock_056
  · exact g32p_row03_decodeBlock_057
  · exact g32p_row03_decodeBlock_058
  · exact g32p_row03_decodeBlock_059
  · exact g32p_row03_decodeBlock_060
  · exact g32p_row03_decodeBlock_061
  · exact g32p_row03_decodeBlock_062
  · exact g32p_row03_decodeBlock_063
  · exact g32p_row03_decodeBlock_064
  · exact g32p_row03_decodeBlock_065
  · exact g32p_row03_decodeBlock_066
  · exact g32p_row03_decodeBlock_067
  · exact g32p_row03_decodeBlock_068
  · exact g32p_row03_decodeBlock_069
  · exact g32p_row03_decodeBlock_070
  · exact g32p_row03_decodeBlock_071
  · exact g32p_row03_decodeBlock_072
  · exact g32p_row03_decodeBlock_073
  · exact g32p_row03_decodeBlock_074
  · exact g32p_row03_decodeBlock_075
  · exact g32p_row03_decodeBlock_076
  · exact g32p_row03_decodeBlock_077
  · exact g32p_row03_decodeBlock_078
  · exact g32p_row03_decodeBlock_079
  · exact g32p_row03_decodeBlock_080
  · exact g32p_row03_decodeBlock_081
  · exact g32p_row03_decodeBlock_082
  · exact g32p_row03_decodeBlock_083
  · exact g32p_row03_decodeBlock_084
  · exact g32p_row03_decodeBlock_085
  · exact g32p_row03_decodeBlock_086
  · exact g32p_row03_decodeBlock_087
  · exact g32p_row03_decodeBlock_088
  · exact g32p_row03_decodeBlock_089
  · exact g32p_row03_decodeBlock_090
  · exact g32p_row03_decodeBlock_091
  · exact g32p_row03_decodeBlock_092
  · exact g32p_row03_decodeBlock_093
  · exact g32p_row03_decodeBlock_094
  · exact g32p_row03_decodeBlock_095
  · exact g32p_row03_decodeBlock_096
  · exact g32p_row03_decodeBlock_097
  · exact g32p_row03_decodeBlock_098
  · exact g32p_row03_decodeBlock_099
  · exact g32p_row03_decodeBlock_100
  · exact g32p_row03_decodeBlock_101
  · exact g32p_row03_decodeBlock_102
  · exact g32p_row03_decodeBlock_103
  · exact g32p_row03_decodeBlock_104
  · exact g32p_row03_decodeBlock_105
  · exact g32p_row03_decodeBlock_106
  · exact g32p_row03_decodeBlock_107
  · exact g32p_row03_decodeBlock_108
  · exact g32p_row03_decodeBlock_109
  · exact g32p_row03_decodeBlock_110
  · exact g32p_row03_decodeBlock_111
  · exact g32p_row03_decodeBlock_112
  · exact g32p_row03_decodeBlock_113
  · exact g32p_row03_decodeBlock_114
  · exact g32p_row03_decodeBlock_115
  · exact g32p_row03_decodeBlock_116
  · exact g32p_row03_decodeBlock_117
  · exact g32p_row03_decodeBlock_118
  · exact g32p_row03_decodeBlock_119
  · exact g32p_row03_decodeBlock_120
  · exact g32p_row03_decodeBlock_121
  · exact g32p_row03_decodeBlock_122
  · exact g32p_row03_decodeBlock_123
  · exact g32p_row03_decodeBlock_124
  · exact g32p_row03_decodeBlock_125
  · exact g32p_row03_decodeBlock_126
  · exact g32p_row03_decodeBlock_127
  · exact g32p_row03_decodeBlock_128
  · exact g32p_row03_decodeBlock_129
  · exact g32p_row03_decodeBlock_130
  · exact g32p_row03_decodeBlock_131
  · exact g32p_row03_decodeBlock_132
  · exact g32p_row03_decodeBlock_133
  · exact g32p_row03_decodeBlock_134
  · exact g32p_row03_decodeBlock_135
  · exact g32p_row03_decodeBlock_136
  · exact g32p_row03_decodeBlock_137
  · exact g32p_row03_decodeBlock_138
  · exact g32p_row03_decodeBlock_139
  · exact g32p_row03_decodeBlock_140
  · exact g32p_row03_decodeBlock_141
  · exact g32p_row03_decodeBlock_142
  · exact g32p_row03_decodeBlock_143
  · exact g32p_row03_decodeBlock_144
  · exact g32p_row03_decodeBlock_145
  · exact g32p_row03_decodeBlock_146
  · exact g32p_row03_decodeBlock_147
  · exact g32p_row03_decodeBlock_148
  · exact g32p_row03_decodeBlock_149
  · exact g32p_row03_decodeBlock_150
  · exact g32p_row03_decodeBlock_151
  · exact g32p_row03_decodeBlock_152
  · exact g32p_row03_decodeBlock_153
  · exact g32p_row03_decodeBlock_154
  · exact g32p_row03_decodeBlock_155
  · exact g32p_row03_decodeBlock_156
  · exact g32p_row03_decodeBlock_157
  · exact g32p_row03_decodeBlock_158
  · exact g32p_row03_decodeBlock_159
  · exact g32p_row03_decodeBlock_160
  · exact g32p_row03_decodeBlock_161
  · exact g32p_row03_decodeBlock_162
  · exact g32p_row03_decodeBlock_163
  · exact g32p_row03_decodeBlock_164
  · exact g32p_row03_decodeBlock_165
  · exact g32p_row03_decodeBlock_166
  · exact g32p_row03_decodeBlock_167
  · exact g32p_row03_decodeBlock_168
  · exact g32p_row03_decodeBlock_169
  · exact g32p_row03_decodeBlock_170
  · exact g32p_row03_decodeBlock_171
  · exact g32p_row03_decodeBlock_172
  · exact g32p_row03_decodeBlock_173
  · exact g32p_row03_decodeBlock_174
  · exact g32p_row03_decodeBlock_175
  · exact g32p_row03_decodeBlock_176
  · exact g32p_row03_decodeBlock_177
  · exact g32p_row03_decodeBlock_178
  · exact g32p_row03_decodeBlock_179
  · exact g32p_row03_decodeBlock_180
  · exact g32p_row03_decodeBlock_181
  · exact g32p_row03_decodeBlock_182
  · exact g32p_row03_decodeBlock_183
  · exact g32p_row03_decodeBlock_184
  · exact g32p_row03_decodeBlock_185
  · exact g32p_row03_decodeBlock_186
  · exact g32p_row03_decodeBlock_187
  · exact g32p_row03_decodeBlock_188
  · exact g32p_row03_decodeBlock_189
  · exact g32p_row03_decodeBlock_190
  · exact g32p_row03_decodeBlock_191
  · exact g32p_row03_decodeBlock_192
  · exact g32p_row03_decodeBlock_193
  · exact g32p_row03_decodeBlock_194
  · exact g32p_row03_decodeBlock_195
  · exact g32p_row03_decodeBlock_196
  · exact g32p_row03_decodeBlock_197
  · exact g32p_row03_decodeBlock_198
  · exact g32p_row03_decodeBlock_199
  · exact g32p_row03_decodeBlock_200
  · exact g32p_row03_decodeBlock_201
  · exact g32p_row03_decodeBlock_202
  · exact g32p_row03_decodeBlock_203
  · exact g32p_row03_decodeBlock_204
  · exact g32p_row03_decodeBlock_205
  · exact g32p_row03_decodeBlock_206
  · exact g32p_row03_decodeBlock_207
  · exact g32p_row03_decodeBlock_208
  · exact g32p_row03_decodeBlock_209
  · exact g32p_row03_decodeBlock_210
  · exact g32p_row03_decodeBlock_211
  · exact g32p_row03_decodeBlock_212
  · exact g32p_row03_decodeBlock_213
  · exact g32p_row03_decodeBlock_214
  · exact g32p_row03_decodeBlock_215
  · exact g32p_row03_decodeBlock_216
  · exact g32p_row03_decodeBlock_217
  · exact g32p_row03_decodeBlock_218
  · exact g32p_row03_decodeBlock_219
  · exact g32p_row03_decodeBlock_220
  · exact g32p_row03_decodeBlock_221
  · exact g32p_row03_decodeBlock_222
  · exact g32p_row03_decodeBlock_223
  · exact g32p_row03_decodeBlock_224
  · exact g32p_row03_decodeBlock_225
  · exact g32p_row03_decodeBlock_226
  · exact g32p_row03_decodeBlock_227
  · exact g32p_row03_decodeBlock_228
  · exact g32p_row03_decodeBlock_229
  · exact g32p_row03_decodeBlock_230
  · exact g32p_row03_decodeBlock_231
  · exact g32p_row03_decodeBlock_232
  · exact g32p_row03_decodeBlock_233
  · exact g32p_row03_decodeBlock_234
  · exact g32p_row03_decodeBlock_235
  · exact g32p_row03_decodeBlock_236
  · exact g32p_row03_decodeBlock_237
  · exact g32p_row03_decodeBlock_238
  · exact g32p_row03_decodeBlock_239
  · exact g32p_row03_decodeBlock_240
  · exact g32p_row03_decodeBlock_241
  · exact g32p_row03_decodeBlock_242
  · exact g32p_row03_decodeBlock_243
  · exact g32p_row03_decodeBlock_244
  · exact g32p_row03_decodeBlock_245
  · exact g32p_row03_decodeBlock_246
  · exact g32p_row03_decodeBlock_247
  · exact g32p_row03_decodeBlock_248
  · exact g32p_row03_decodeBlock_249
  · exact g32p_row03_decodeBlock_250
  · exact g32p_row03_decodeBlock_251
  · exact g32p_row03_decodeBlock_252
  · exact g32p_row03_decodeBlock_253
  · exact g32p_row03_decodeBlock_254
  · exact g32p_row03_decodeBlock_255
  · exact g32p_row03_decodeBlock_256
  · exact g32p_row03_decodeBlock_257
  · exact g32p_row03_decodeBlock_258
  · exact g32p_row03_decodeBlock_259
  · exact g32p_row03_decodeBlock_260
  · exact g32p_row03_decodeBlock_261
  · exact g32p_row03_decodeBlock_262
  · exact g32p_row03_decodeBlock_263
  · exact g32p_row03_decodeBlock_264
  · exact g32p_row03_decodeBlock_265
  · exact g32p_row03_decodeBlock_266
  · exact g32p_row03_decodeBlock_267
  · exact g32p_row03_decodeBlock_268
  · exact g32p_row03_decodeBlock_269

theorem g32p_row03_groupInjective : Function.Injective g32p_row03_groupNodes :=
  g32p_matrix_injective_of_decoder _ _ g32p_row03_matrixDecode_leftInverse


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_groupParent_lt : ∀ i : Fin 4320, i ≠ 0 →
    (g32p_row03_groupParent i).val < i.val := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row03_parentLtBlock_000
  · exact g32p_row03_parentLtBlock_001
  · exact g32p_row03_parentLtBlock_002
  · exact g32p_row03_parentLtBlock_003
  · exact g32p_row03_parentLtBlock_004
  · exact g32p_row03_parentLtBlock_005
  · exact g32p_row03_parentLtBlock_006
  · exact g32p_row03_parentLtBlock_007
  · exact g32p_row03_parentLtBlock_008
  · exact g32p_row03_parentLtBlock_009
  · exact g32p_row03_parentLtBlock_010
  · exact g32p_row03_parentLtBlock_011
  · exact g32p_row03_parentLtBlock_012
  · exact g32p_row03_parentLtBlock_013
  · exact g32p_row03_parentLtBlock_014
  · exact g32p_row03_parentLtBlock_015
  · exact g32p_row03_parentLtBlock_016
  · exact g32p_row03_parentLtBlock_017
  · exact g32p_row03_parentLtBlock_018
  · exact g32p_row03_parentLtBlock_019
  · exact g32p_row03_parentLtBlock_020
  · exact g32p_row03_parentLtBlock_021
  · exact g32p_row03_parentLtBlock_022
  · exact g32p_row03_parentLtBlock_023
  · exact g32p_row03_parentLtBlock_024
  · exact g32p_row03_parentLtBlock_025
  · exact g32p_row03_parentLtBlock_026
  · exact g32p_row03_parentLtBlock_027
  · exact g32p_row03_parentLtBlock_028
  · exact g32p_row03_parentLtBlock_029
  · exact g32p_row03_parentLtBlock_030
  · exact g32p_row03_parentLtBlock_031
  · exact g32p_row03_parentLtBlock_032
  · exact g32p_row03_parentLtBlock_033
  · exact g32p_row03_parentLtBlock_034
  · exact g32p_row03_parentLtBlock_035
  · exact g32p_row03_parentLtBlock_036
  · exact g32p_row03_parentLtBlock_037
  · exact g32p_row03_parentLtBlock_038
  · exact g32p_row03_parentLtBlock_039
  · exact g32p_row03_parentLtBlock_040
  · exact g32p_row03_parentLtBlock_041
  · exact g32p_row03_parentLtBlock_042
  · exact g32p_row03_parentLtBlock_043
  · exact g32p_row03_parentLtBlock_044
  · exact g32p_row03_parentLtBlock_045
  · exact g32p_row03_parentLtBlock_046
  · exact g32p_row03_parentLtBlock_047
  · exact g32p_row03_parentLtBlock_048
  · exact g32p_row03_parentLtBlock_049
  · exact g32p_row03_parentLtBlock_050
  · exact g32p_row03_parentLtBlock_051
  · exact g32p_row03_parentLtBlock_052
  · exact g32p_row03_parentLtBlock_053
  · exact g32p_row03_parentLtBlock_054
  · exact g32p_row03_parentLtBlock_055
  · exact g32p_row03_parentLtBlock_056
  · exact g32p_row03_parentLtBlock_057
  · exact g32p_row03_parentLtBlock_058
  · exact g32p_row03_parentLtBlock_059
  · exact g32p_row03_parentLtBlock_060
  · exact g32p_row03_parentLtBlock_061
  · exact g32p_row03_parentLtBlock_062
  · exact g32p_row03_parentLtBlock_063
  · exact g32p_row03_parentLtBlock_064
  · exact g32p_row03_parentLtBlock_065
  · exact g32p_row03_parentLtBlock_066
  · exact g32p_row03_parentLtBlock_067
  · exact g32p_row03_parentLtBlock_068
  · exact g32p_row03_parentLtBlock_069
  · exact g32p_row03_parentLtBlock_070
  · exact g32p_row03_parentLtBlock_071
  · exact g32p_row03_parentLtBlock_072
  · exact g32p_row03_parentLtBlock_073
  · exact g32p_row03_parentLtBlock_074
  · exact g32p_row03_parentLtBlock_075
  · exact g32p_row03_parentLtBlock_076
  · exact g32p_row03_parentLtBlock_077
  · exact g32p_row03_parentLtBlock_078
  · exact g32p_row03_parentLtBlock_079
  · exact g32p_row03_parentLtBlock_080
  · exact g32p_row03_parentLtBlock_081
  · exact g32p_row03_parentLtBlock_082
  · exact g32p_row03_parentLtBlock_083
  · exact g32p_row03_parentLtBlock_084
  · exact g32p_row03_parentLtBlock_085
  · exact g32p_row03_parentLtBlock_086
  · exact g32p_row03_parentLtBlock_087
  · exact g32p_row03_parentLtBlock_088
  · exact g32p_row03_parentLtBlock_089
  · exact g32p_row03_parentLtBlock_090
  · exact g32p_row03_parentLtBlock_091
  · exact g32p_row03_parentLtBlock_092
  · exact g32p_row03_parentLtBlock_093
  · exact g32p_row03_parentLtBlock_094
  · exact g32p_row03_parentLtBlock_095
  · exact g32p_row03_parentLtBlock_096
  · exact g32p_row03_parentLtBlock_097
  · exact g32p_row03_parentLtBlock_098
  · exact g32p_row03_parentLtBlock_099
  · exact g32p_row03_parentLtBlock_100
  · exact g32p_row03_parentLtBlock_101
  · exact g32p_row03_parentLtBlock_102
  · exact g32p_row03_parentLtBlock_103
  · exact g32p_row03_parentLtBlock_104
  · exact g32p_row03_parentLtBlock_105
  · exact g32p_row03_parentLtBlock_106
  · exact g32p_row03_parentLtBlock_107
  · exact g32p_row03_parentLtBlock_108
  · exact g32p_row03_parentLtBlock_109
  · exact g32p_row03_parentLtBlock_110
  · exact g32p_row03_parentLtBlock_111
  · exact g32p_row03_parentLtBlock_112
  · exact g32p_row03_parentLtBlock_113
  · exact g32p_row03_parentLtBlock_114
  · exact g32p_row03_parentLtBlock_115
  · exact g32p_row03_parentLtBlock_116
  · exact g32p_row03_parentLtBlock_117
  · exact g32p_row03_parentLtBlock_118
  · exact g32p_row03_parentLtBlock_119
  · exact g32p_row03_parentLtBlock_120
  · exact g32p_row03_parentLtBlock_121
  · exact g32p_row03_parentLtBlock_122
  · exact g32p_row03_parentLtBlock_123
  · exact g32p_row03_parentLtBlock_124
  · exact g32p_row03_parentLtBlock_125
  · exact g32p_row03_parentLtBlock_126
  · exact g32p_row03_parentLtBlock_127
  · exact g32p_row03_parentLtBlock_128
  · exact g32p_row03_parentLtBlock_129
  · exact g32p_row03_parentLtBlock_130
  · exact g32p_row03_parentLtBlock_131
  · exact g32p_row03_parentLtBlock_132
  · exact g32p_row03_parentLtBlock_133
  · exact g32p_row03_parentLtBlock_134
  · exact g32p_row03_parentLtBlock_135
  · exact g32p_row03_parentLtBlock_136
  · exact g32p_row03_parentLtBlock_137
  · exact g32p_row03_parentLtBlock_138
  · exact g32p_row03_parentLtBlock_139
  · exact g32p_row03_parentLtBlock_140
  · exact g32p_row03_parentLtBlock_141
  · exact g32p_row03_parentLtBlock_142
  · exact g32p_row03_parentLtBlock_143
  · exact g32p_row03_parentLtBlock_144
  · exact g32p_row03_parentLtBlock_145
  · exact g32p_row03_parentLtBlock_146
  · exact g32p_row03_parentLtBlock_147
  · exact g32p_row03_parentLtBlock_148
  · exact g32p_row03_parentLtBlock_149
  · exact g32p_row03_parentLtBlock_150
  · exact g32p_row03_parentLtBlock_151
  · exact g32p_row03_parentLtBlock_152
  · exact g32p_row03_parentLtBlock_153
  · exact g32p_row03_parentLtBlock_154
  · exact g32p_row03_parentLtBlock_155
  · exact g32p_row03_parentLtBlock_156
  · exact g32p_row03_parentLtBlock_157
  · exact g32p_row03_parentLtBlock_158
  · exact g32p_row03_parentLtBlock_159
  · exact g32p_row03_parentLtBlock_160
  · exact g32p_row03_parentLtBlock_161
  · exact g32p_row03_parentLtBlock_162
  · exact g32p_row03_parentLtBlock_163
  · exact g32p_row03_parentLtBlock_164
  · exact g32p_row03_parentLtBlock_165
  · exact g32p_row03_parentLtBlock_166
  · exact g32p_row03_parentLtBlock_167
  · exact g32p_row03_parentLtBlock_168
  · exact g32p_row03_parentLtBlock_169
  · exact g32p_row03_parentLtBlock_170
  · exact g32p_row03_parentLtBlock_171
  · exact g32p_row03_parentLtBlock_172
  · exact g32p_row03_parentLtBlock_173
  · exact g32p_row03_parentLtBlock_174
  · exact g32p_row03_parentLtBlock_175
  · exact g32p_row03_parentLtBlock_176
  · exact g32p_row03_parentLtBlock_177
  · exact g32p_row03_parentLtBlock_178
  · exact g32p_row03_parentLtBlock_179
  · exact g32p_row03_parentLtBlock_180
  · exact g32p_row03_parentLtBlock_181
  · exact g32p_row03_parentLtBlock_182
  · exact g32p_row03_parentLtBlock_183
  · exact g32p_row03_parentLtBlock_184
  · exact g32p_row03_parentLtBlock_185
  · exact g32p_row03_parentLtBlock_186
  · exact g32p_row03_parentLtBlock_187
  · exact g32p_row03_parentLtBlock_188
  · exact g32p_row03_parentLtBlock_189
  · exact g32p_row03_parentLtBlock_190
  · exact g32p_row03_parentLtBlock_191
  · exact g32p_row03_parentLtBlock_192
  · exact g32p_row03_parentLtBlock_193
  · exact g32p_row03_parentLtBlock_194
  · exact g32p_row03_parentLtBlock_195
  · exact g32p_row03_parentLtBlock_196
  · exact g32p_row03_parentLtBlock_197
  · exact g32p_row03_parentLtBlock_198
  · exact g32p_row03_parentLtBlock_199
  · exact g32p_row03_parentLtBlock_200
  · exact g32p_row03_parentLtBlock_201
  · exact g32p_row03_parentLtBlock_202
  · exact g32p_row03_parentLtBlock_203
  · exact g32p_row03_parentLtBlock_204
  · exact g32p_row03_parentLtBlock_205
  · exact g32p_row03_parentLtBlock_206
  · exact g32p_row03_parentLtBlock_207
  · exact g32p_row03_parentLtBlock_208
  · exact g32p_row03_parentLtBlock_209
  · exact g32p_row03_parentLtBlock_210
  · exact g32p_row03_parentLtBlock_211
  · exact g32p_row03_parentLtBlock_212
  · exact g32p_row03_parentLtBlock_213
  · exact g32p_row03_parentLtBlock_214
  · exact g32p_row03_parentLtBlock_215
  · exact g32p_row03_parentLtBlock_216
  · exact g32p_row03_parentLtBlock_217
  · exact g32p_row03_parentLtBlock_218
  · exact g32p_row03_parentLtBlock_219
  · exact g32p_row03_parentLtBlock_220
  · exact g32p_row03_parentLtBlock_221
  · exact g32p_row03_parentLtBlock_222
  · exact g32p_row03_parentLtBlock_223
  · exact g32p_row03_parentLtBlock_224
  · exact g32p_row03_parentLtBlock_225
  · exact g32p_row03_parentLtBlock_226
  · exact g32p_row03_parentLtBlock_227
  · exact g32p_row03_parentLtBlock_228
  · exact g32p_row03_parentLtBlock_229
  · exact g32p_row03_parentLtBlock_230
  · exact g32p_row03_parentLtBlock_231
  · exact g32p_row03_parentLtBlock_232
  · exact g32p_row03_parentLtBlock_233
  · exact g32p_row03_parentLtBlock_234
  · exact g32p_row03_parentLtBlock_235
  · exact g32p_row03_parentLtBlock_236
  · exact g32p_row03_parentLtBlock_237
  · exact g32p_row03_parentLtBlock_238
  · exact g32p_row03_parentLtBlock_239
  · exact g32p_row03_parentLtBlock_240
  · exact g32p_row03_parentLtBlock_241
  · exact g32p_row03_parentLtBlock_242
  · exact g32p_row03_parentLtBlock_243
  · exact g32p_row03_parentLtBlock_244
  · exact g32p_row03_parentLtBlock_245
  · exact g32p_row03_parentLtBlock_246
  · exact g32p_row03_parentLtBlock_247
  · exact g32p_row03_parentLtBlock_248
  · exact g32p_row03_parentLtBlock_249
  · exact g32p_row03_parentLtBlock_250
  · exact g32p_row03_parentLtBlock_251
  · exact g32p_row03_parentLtBlock_252
  · exact g32p_row03_parentLtBlock_253
  · exact g32p_row03_parentLtBlock_254
  · exact g32p_row03_parentLtBlock_255
  · exact g32p_row03_parentLtBlock_256
  · exact g32p_row03_parentLtBlock_257
  · exact g32p_row03_parentLtBlock_258
  · exact g32p_row03_parentLtBlock_259
  · exact g32p_row03_parentLtBlock_260
  · exact g32p_row03_parentLtBlock_261
  · exact g32p_row03_parentLtBlock_262
  · exact g32p_row03_parentLtBlock_263
  · exact g32p_row03_parentLtBlock_264
  · exact g32p_row03_parentLtBlock_265
  · exact g32p_row03_parentLtBlock_266
  · exact g32p_row03_parentLtBlock_267
  · exact g32p_row03_parentLtBlock_268
  · exact g32p_row03_parentLtBlock_269

theorem g32p_row03_groupParent_step : ∀ i : Fin 4320, i ≠ 0 →
    g32p_row03_groupNext (g32p_row03_groupParent i) (g32p_row03_groupLabel i) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row03_parentStepBlock_000
  · exact g32p_row03_parentStepBlock_001
  · exact g32p_row03_parentStepBlock_002
  · exact g32p_row03_parentStepBlock_003
  · exact g32p_row03_parentStepBlock_004
  · exact g32p_row03_parentStepBlock_005
  · exact g32p_row03_parentStepBlock_006
  · exact g32p_row03_parentStepBlock_007
  · exact g32p_row03_parentStepBlock_008
  · exact g32p_row03_parentStepBlock_009
  · exact g32p_row03_parentStepBlock_010
  · exact g32p_row03_parentStepBlock_011
  · exact g32p_row03_parentStepBlock_012
  · exact g32p_row03_parentStepBlock_013
  · exact g32p_row03_parentStepBlock_014
  · exact g32p_row03_parentStepBlock_015
  · exact g32p_row03_parentStepBlock_016
  · exact g32p_row03_parentStepBlock_017
  · exact g32p_row03_parentStepBlock_018
  · exact g32p_row03_parentStepBlock_019
  · exact g32p_row03_parentStepBlock_020
  · exact g32p_row03_parentStepBlock_021
  · exact g32p_row03_parentStepBlock_022
  · exact g32p_row03_parentStepBlock_023
  · exact g32p_row03_parentStepBlock_024
  · exact g32p_row03_parentStepBlock_025
  · exact g32p_row03_parentStepBlock_026
  · exact g32p_row03_parentStepBlock_027
  · exact g32p_row03_parentStepBlock_028
  · exact g32p_row03_parentStepBlock_029
  · exact g32p_row03_parentStepBlock_030
  · exact g32p_row03_parentStepBlock_031
  · exact g32p_row03_parentStepBlock_032
  · exact g32p_row03_parentStepBlock_033
  · exact g32p_row03_parentStepBlock_034
  · exact g32p_row03_parentStepBlock_035
  · exact g32p_row03_parentStepBlock_036
  · exact g32p_row03_parentStepBlock_037
  · exact g32p_row03_parentStepBlock_038
  · exact g32p_row03_parentStepBlock_039
  · exact g32p_row03_parentStepBlock_040
  · exact g32p_row03_parentStepBlock_041
  · exact g32p_row03_parentStepBlock_042
  · exact g32p_row03_parentStepBlock_043
  · exact g32p_row03_parentStepBlock_044
  · exact g32p_row03_parentStepBlock_045
  · exact g32p_row03_parentStepBlock_046
  · exact g32p_row03_parentStepBlock_047
  · exact g32p_row03_parentStepBlock_048
  · exact g32p_row03_parentStepBlock_049
  · exact g32p_row03_parentStepBlock_050
  · exact g32p_row03_parentStepBlock_051
  · exact g32p_row03_parentStepBlock_052
  · exact g32p_row03_parentStepBlock_053
  · exact g32p_row03_parentStepBlock_054
  · exact g32p_row03_parentStepBlock_055
  · exact g32p_row03_parentStepBlock_056
  · exact g32p_row03_parentStepBlock_057
  · exact g32p_row03_parentStepBlock_058
  · exact g32p_row03_parentStepBlock_059
  · exact g32p_row03_parentStepBlock_060
  · exact g32p_row03_parentStepBlock_061
  · exact g32p_row03_parentStepBlock_062
  · exact g32p_row03_parentStepBlock_063
  · exact g32p_row03_parentStepBlock_064
  · exact g32p_row03_parentStepBlock_065
  · exact g32p_row03_parentStepBlock_066
  · exact g32p_row03_parentStepBlock_067
  · exact g32p_row03_parentStepBlock_068
  · exact g32p_row03_parentStepBlock_069
  · exact g32p_row03_parentStepBlock_070
  · exact g32p_row03_parentStepBlock_071
  · exact g32p_row03_parentStepBlock_072
  · exact g32p_row03_parentStepBlock_073
  · exact g32p_row03_parentStepBlock_074
  · exact g32p_row03_parentStepBlock_075
  · exact g32p_row03_parentStepBlock_076
  · exact g32p_row03_parentStepBlock_077
  · exact g32p_row03_parentStepBlock_078
  · exact g32p_row03_parentStepBlock_079
  · exact g32p_row03_parentStepBlock_080
  · exact g32p_row03_parentStepBlock_081
  · exact g32p_row03_parentStepBlock_082
  · exact g32p_row03_parentStepBlock_083
  · exact g32p_row03_parentStepBlock_084
  · exact g32p_row03_parentStepBlock_085
  · exact g32p_row03_parentStepBlock_086
  · exact g32p_row03_parentStepBlock_087
  · exact g32p_row03_parentStepBlock_088
  · exact g32p_row03_parentStepBlock_089
  · exact g32p_row03_parentStepBlock_090
  · exact g32p_row03_parentStepBlock_091
  · exact g32p_row03_parentStepBlock_092
  · exact g32p_row03_parentStepBlock_093
  · exact g32p_row03_parentStepBlock_094
  · exact g32p_row03_parentStepBlock_095
  · exact g32p_row03_parentStepBlock_096
  · exact g32p_row03_parentStepBlock_097
  · exact g32p_row03_parentStepBlock_098
  · exact g32p_row03_parentStepBlock_099
  · exact g32p_row03_parentStepBlock_100
  · exact g32p_row03_parentStepBlock_101
  · exact g32p_row03_parentStepBlock_102
  · exact g32p_row03_parentStepBlock_103
  · exact g32p_row03_parentStepBlock_104
  · exact g32p_row03_parentStepBlock_105
  · exact g32p_row03_parentStepBlock_106
  · exact g32p_row03_parentStepBlock_107
  · exact g32p_row03_parentStepBlock_108
  · exact g32p_row03_parentStepBlock_109
  · exact g32p_row03_parentStepBlock_110
  · exact g32p_row03_parentStepBlock_111
  · exact g32p_row03_parentStepBlock_112
  · exact g32p_row03_parentStepBlock_113
  · exact g32p_row03_parentStepBlock_114
  · exact g32p_row03_parentStepBlock_115
  · exact g32p_row03_parentStepBlock_116
  · exact g32p_row03_parentStepBlock_117
  · exact g32p_row03_parentStepBlock_118
  · exact g32p_row03_parentStepBlock_119
  · exact g32p_row03_parentStepBlock_120
  · exact g32p_row03_parentStepBlock_121
  · exact g32p_row03_parentStepBlock_122
  · exact g32p_row03_parentStepBlock_123
  · exact g32p_row03_parentStepBlock_124
  · exact g32p_row03_parentStepBlock_125
  · exact g32p_row03_parentStepBlock_126
  · exact g32p_row03_parentStepBlock_127
  · exact g32p_row03_parentStepBlock_128
  · exact g32p_row03_parentStepBlock_129
  · exact g32p_row03_parentStepBlock_130
  · exact g32p_row03_parentStepBlock_131
  · exact g32p_row03_parentStepBlock_132
  · exact g32p_row03_parentStepBlock_133
  · exact g32p_row03_parentStepBlock_134
  · exact g32p_row03_parentStepBlock_135
  · exact g32p_row03_parentStepBlock_136
  · exact g32p_row03_parentStepBlock_137
  · exact g32p_row03_parentStepBlock_138
  · exact g32p_row03_parentStepBlock_139
  · exact g32p_row03_parentStepBlock_140
  · exact g32p_row03_parentStepBlock_141
  · exact g32p_row03_parentStepBlock_142
  · exact g32p_row03_parentStepBlock_143
  · exact g32p_row03_parentStepBlock_144
  · exact g32p_row03_parentStepBlock_145
  · exact g32p_row03_parentStepBlock_146
  · exact g32p_row03_parentStepBlock_147
  · exact g32p_row03_parentStepBlock_148
  · exact g32p_row03_parentStepBlock_149
  · exact g32p_row03_parentStepBlock_150
  · exact g32p_row03_parentStepBlock_151
  · exact g32p_row03_parentStepBlock_152
  · exact g32p_row03_parentStepBlock_153
  · exact g32p_row03_parentStepBlock_154
  · exact g32p_row03_parentStepBlock_155
  · exact g32p_row03_parentStepBlock_156
  · exact g32p_row03_parentStepBlock_157
  · exact g32p_row03_parentStepBlock_158
  · exact g32p_row03_parentStepBlock_159
  · exact g32p_row03_parentStepBlock_160
  · exact g32p_row03_parentStepBlock_161
  · exact g32p_row03_parentStepBlock_162
  · exact g32p_row03_parentStepBlock_163
  · exact g32p_row03_parentStepBlock_164
  · exact g32p_row03_parentStepBlock_165
  · exact g32p_row03_parentStepBlock_166
  · exact g32p_row03_parentStepBlock_167
  · exact g32p_row03_parentStepBlock_168
  · exact g32p_row03_parentStepBlock_169
  · exact g32p_row03_parentStepBlock_170
  · exact g32p_row03_parentStepBlock_171
  · exact g32p_row03_parentStepBlock_172
  · exact g32p_row03_parentStepBlock_173
  · exact g32p_row03_parentStepBlock_174
  · exact g32p_row03_parentStepBlock_175
  · exact g32p_row03_parentStepBlock_176
  · exact g32p_row03_parentStepBlock_177
  · exact g32p_row03_parentStepBlock_178
  · exact g32p_row03_parentStepBlock_179
  · exact g32p_row03_parentStepBlock_180
  · exact g32p_row03_parentStepBlock_181
  · exact g32p_row03_parentStepBlock_182
  · exact g32p_row03_parentStepBlock_183
  · exact g32p_row03_parentStepBlock_184
  · exact g32p_row03_parentStepBlock_185
  · exact g32p_row03_parentStepBlock_186
  · exact g32p_row03_parentStepBlock_187
  · exact g32p_row03_parentStepBlock_188
  · exact g32p_row03_parentStepBlock_189
  · exact g32p_row03_parentStepBlock_190
  · exact g32p_row03_parentStepBlock_191
  · exact g32p_row03_parentStepBlock_192
  · exact g32p_row03_parentStepBlock_193
  · exact g32p_row03_parentStepBlock_194
  · exact g32p_row03_parentStepBlock_195
  · exact g32p_row03_parentStepBlock_196
  · exact g32p_row03_parentStepBlock_197
  · exact g32p_row03_parentStepBlock_198
  · exact g32p_row03_parentStepBlock_199
  · exact g32p_row03_parentStepBlock_200
  · exact g32p_row03_parentStepBlock_201
  · exact g32p_row03_parentStepBlock_202
  · exact g32p_row03_parentStepBlock_203
  · exact g32p_row03_parentStepBlock_204
  · exact g32p_row03_parentStepBlock_205
  · exact g32p_row03_parentStepBlock_206
  · exact g32p_row03_parentStepBlock_207
  · exact g32p_row03_parentStepBlock_208
  · exact g32p_row03_parentStepBlock_209
  · exact g32p_row03_parentStepBlock_210
  · exact g32p_row03_parentStepBlock_211
  · exact g32p_row03_parentStepBlock_212
  · exact g32p_row03_parentStepBlock_213
  · exact g32p_row03_parentStepBlock_214
  · exact g32p_row03_parentStepBlock_215
  · exact g32p_row03_parentStepBlock_216
  · exact g32p_row03_parentStepBlock_217
  · exact g32p_row03_parentStepBlock_218
  · exact g32p_row03_parentStepBlock_219
  · exact g32p_row03_parentStepBlock_220
  · exact g32p_row03_parentStepBlock_221
  · exact g32p_row03_parentStepBlock_222
  · exact g32p_row03_parentStepBlock_223
  · exact g32p_row03_parentStepBlock_224
  · exact g32p_row03_parentStepBlock_225
  · exact g32p_row03_parentStepBlock_226
  · exact g32p_row03_parentStepBlock_227
  · exact g32p_row03_parentStepBlock_228
  · exact g32p_row03_parentStepBlock_229
  · exact g32p_row03_parentStepBlock_230
  · exact g32p_row03_parentStepBlock_231
  · exact g32p_row03_parentStepBlock_232
  · exact g32p_row03_parentStepBlock_233
  · exact g32p_row03_parentStepBlock_234
  · exact g32p_row03_parentStepBlock_235
  · exact g32p_row03_parentStepBlock_236
  · exact g32p_row03_parentStepBlock_237
  · exact g32p_row03_parentStepBlock_238
  · exact g32p_row03_parentStepBlock_239
  · exact g32p_row03_parentStepBlock_240
  · exact g32p_row03_parentStepBlock_241
  · exact g32p_row03_parentStepBlock_242
  · exact g32p_row03_parentStepBlock_243
  · exact g32p_row03_parentStepBlock_244
  · exact g32p_row03_parentStepBlock_245
  · exact g32p_row03_parentStepBlock_246
  · exact g32p_row03_parentStepBlock_247
  · exact g32p_row03_parentStepBlock_248
  · exact g32p_row03_parentStepBlock_249
  · exact g32p_row03_parentStepBlock_250
  · exact g32p_row03_parentStepBlock_251
  · exact g32p_row03_parentStepBlock_252
  · exact g32p_row03_parentStepBlock_253
  · exact g32p_row03_parentStepBlock_254
  · exact g32p_row03_parentStepBlock_255
  · exact g32p_row03_parentStepBlock_256
  · exact g32p_row03_parentStepBlock_257
  · exact g32p_row03_parentStepBlock_258
  · exact g32p_row03_parentStepBlock_259
  · exact g32p_row03_parentStepBlock_260
  · exact g32p_row03_parentStepBlock_261
  · exact g32p_row03_parentStepBlock_262
  · exact g32p_row03_parentStepBlock_263
  · exact g32p_row03_parentStepBlock_264
  · exact g32p_row03_parentStepBlock_265
  · exact g32p_row03_parentStepBlock_266
  · exact g32p_row03_parentStepBlock_267
  · exact g32p_row03_parentStepBlock_268
  · exact g32p_row03_parentStepBlock_269


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_groupEnumeration :
    ∃ e : Fin 4320 ≃ Subgroup.closure (Set.range g32p_row03_groupGenerators),
      ∀ i, b4b_toMatrix (e i : g32p_G) =
        HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
          (g32p_row03_groupNodes i)) := by
  apply g32p_matrixPathEnumeration b4b_toMatrix Subtype.val_injective
    (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (by rw [HurwitzPrymRex_evM_mone, map_one])
    (by intro a b; rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul])
    (HurwitzPrymRex_g32conj_injective.comp
      (HurwitzPrymRex_evM_injective g32h_omega_sq_add))
    g32p_row03_groupGenerators g32p_row03_groupMatrices g32p_row03_groupGenerator_map
    g32p_row03_groupNodes 0 g32p_row03_groupParent g32p_row03_groupLabel Fin.val
    g32p_row03_groupNext g32p_row03_groupInjective (by decide)
    g32p_row03_groupParent_lt
  · intro i hi
    have hs := g32p_row03_groupStep
      (g32p_row03_groupParent i) (g32p_row03_groupLabel i)
    rw [g32p_row03_groupParent_step i hi] at hs
    exact hs.symm
  · exact g32p_row03_groupStep

theorem g32p_row03_groupOrder :
    Nat.card (Subgroup.closure (Set.range g32p_row03_groupGenerators)) = 4320 := by
  obtain ⟨e, _⟩ := g32p_row03_groupEnumeration
  simpa only [Nat.card_fin] using (Nat.card_congr e).symm

def g32p_row03_groupEquiv : Fin 4320 ≃ Subgroup.closure (Set.range g32p_row03_groupGenerators) :=
  Classical.choose g32p_row03_groupEnumeration

theorem g32p_row03_groupEquiv_map (i : Fin 4320) :
    b4b_toMatrix (g32p_row03_groupEquiv i : g32p_G) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row03_groupNodes i)) :=
  Classical.choose_spec g32p_row03_groupEnumeration i

theorem g32p_row03_groupEquiv_one : g32p_row03_groupEquiv 0 = 1 := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row03_groupEquiv 0 : g32p_G) = b4b_toMatrix 1
  rw [g32p_row03_groupEquiv_map, map_one,
    show g32p_row03_groupNodes 0 = HurwitzPrymRex_mone by decide,
    HurwitzPrymRex_evM_mone, map_one]

theorem g32p_row03_groupEquiv_step (i : Fin 4320) (s : Fin 2) :
    g32p_row03_groupEquiv (g32p_row03_groupNext i s) =
      g32p_row03_groupEquiv i *
        ⟨g32p_row03_groupGenerators s, Subgroup.subset_closure (Set.mem_range_self s)⟩ := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row03_groupEquiv (g32p_row03_groupNext i s) : g32p_G) =
    b4b_toMatrix ((g32p_row03_groupEquiv i : g32p_G) * g32p_row03_groupGenerators s)
  rw [map_mul, g32p_row03_groupEquiv_map, g32p_row03_groupEquiv_map,
    g32p_row03_groupGenerator_map, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  exact congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (g32p_row03_groupStep i s).symm


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_characterTransition : ∀ i : Fin 4320, ∀ s : Fin 2,
    g32p_row03_characterValues (g32p_row03_groupNext i s) =
      g32p_row03_characterValues i * g32p_row03_characterValues (g32p_row03_groupNext 0 s) := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row03_characterBlock_000
  · exact g32p_row03_characterBlock_001
  · exact g32p_row03_characterBlock_002
  · exact g32p_row03_characterBlock_003
  · exact g32p_row03_characterBlock_004
  · exact g32p_row03_characterBlock_005
  · exact g32p_row03_characterBlock_006
  · exact g32p_row03_characterBlock_007
  · exact g32p_row03_characterBlock_008
  · exact g32p_row03_characterBlock_009
  · exact g32p_row03_characterBlock_010
  · exact g32p_row03_characterBlock_011
  · exact g32p_row03_characterBlock_012
  · exact g32p_row03_characterBlock_013
  · exact g32p_row03_characterBlock_014
  · exact g32p_row03_characterBlock_015
  · exact g32p_row03_characterBlock_016
  · exact g32p_row03_characterBlock_017
  · exact g32p_row03_characterBlock_018
  · exact g32p_row03_characterBlock_019
  · exact g32p_row03_characterBlock_020
  · exact g32p_row03_characterBlock_021
  · exact g32p_row03_characterBlock_022
  · exact g32p_row03_characterBlock_023
  · exact g32p_row03_characterBlock_024
  · exact g32p_row03_characterBlock_025
  · exact g32p_row03_characterBlock_026
  · exact g32p_row03_characterBlock_027
  · exact g32p_row03_characterBlock_028
  · exact g32p_row03_characterBlock_029
  · exact g32p_row03_characterBlock_030
  · exact g32p_row03_characterBlock_031
  · exact g32p_row03_characterBlock_032
  · exact g32p_row03_characterBlock_033
  · exact g32p_row03_characterBlock_034
  · exact g32p_row03_characterBlock_035
  · exact g32p_row03_characterBlock_036
  · exact g32p_row03_characterBlock_037
  · exact g32p_row03_characterBlock_038
  · exact g32p_row03_characterBlock_039
  · exact g32p_row03_characterBlock_040
  · exact g32p_row03_characterBlock_041
  · exact g32p_row03_characterBlock_042
  · exact g32p_row03_characterBlock_043
  · exact g32p_row03_characterBlock_044
  · exact g32p_row03_characterBlock_045
  · exact g32p_row03_characterBlock_046
  · exact g32p_row03_characterBlock_047
  · exact g32p_row03_characterBlock_048
  · exact g32p_row03_characterBlock_049
  · exact g32p_row03_characterBlock_050
  · exact g32p_row03_characterBlock_051
  · exact g32p_row03_characterBlock_052
  · exact g32p_row03_characterBlock_053
  · exact g32p_row03_characterBlock_054
  · exact g32p_row03_characterBlock_055
  · exact g32p_row03_characterBlock_056
  · exact g32p_row03_characterBlock_057
  · exact g32p_row03_characterBlock_058
  · exact g32p_row03_characterBlock_059
  · exact g32p_row03_characterBlock_060
  · exact g32p_row03_characterBlock_061
  · exact g32p_row03_characterBlock_062
  · exact g32p_row03_characterBlock_063
  · exact g32p_row03_characterBlock_064
  · exact g32p_row03_characterBlock_065
  · exact g32p_row03_characterBlock_066
  · exact g32p_row03_characterBlock_067
  · exact g32p_row03_characterBlock_068
  · exact g32p_row03_characterBlock_069
  · exact g32p_row03_characterBlock_070
  · exact g32p_row03_characterBlock_071
  · exact g32p_row03_characterBlock_072
  · exact g32p_row03_characterBlock_073
  · exact g32p_row03_characterBlock_074
  · exact g32p_row03_characterBlock_075
  · exact g32p_row03_characterBlock_076
  · exact g32p_row03_characterBlock_077
  · exact g32p_row03_characterBlock_078
  · exact g32p_row03_characterBlock_079
  · exact g32p_row03_characterBlock_080
  · exact g32p_row03_characterBlock_081
  · exact g32p_row03_characterBlock_082
  · exact g32p_row03_characterBlock_083
  · exact g32p_row03_characterBlock_084
  · exact g32p_row03_characterBlock_085
  · exact g32p_row03_characterBlock_086
  · exact g32p_row03_characterBlock_087
  · exact g32p_row03_characterBlock_088
  · exact g32p_row03_characterBlock_089
  · exact g32p_row03_characterBlock_090
  · exact g32p_row03_characterBlock_091
  · exact g32p_row03_characterBlock_092
  · exact g32p_row03_characterBlock_093
  · exact g32p_row03_characterBlock_094
  · exact g32p_row03_characterBlock_095
  · exact g32p_row03_characterBlock_096
  · exact g32p_row03_characterBlock_097
  · exact g32p_row03_characterBlock_098
  · exact g32p_row03_characterBlock_099
  · exact g32p_row03_characterBlock_100
  · exact g32p_row03_characterBlock_101
  · exact g32p_row03_characterBlock_102
  · exact g32p_row03_characterBlock_103
  · exact g32p_row03_characterBlock_104
  · exact g32p_row03_characterBlock_105
  · exact g32p_row03_characterBlock_106
  · exact g32p_row03_characterBlock_107
  · exact g32p_row03_characterBlock_108
  · exact g32p_row03_characterBlock_109
  · exact g32p_row03_characterBlock_110
  · exact g32p_row03_characterBlock_111
  · exact g32p_row03_characterBlock_112
  · exact g32p_row03_characterBlock_113
  · exact g32p_row03_characterBlock_114
  · exact g32p_row03_characterBlock_115
  · exact g32p_row03_characterBlock_116
  · exact g32p_row03_characterBlock_117
  · exact g32p_row03_characterBlock_118
  · exact g32p_row03_characterBlock_119
  · exact g32p_row03_characterBlock_120
  · exact g32p_row03_characterBlock_121
  · exact g32p_row03_characterBlock_122
  · exact g32p_row03_characterBlock_123
  · exact g32p_row03_characterBlock_124
  · exact g32p_row03_characterBlock_125
  · exact g32p_row03_characterBlock_126
  · exact g32p_row03_characterBlock_127
  · exact g32p_row03_characterBlock_128
  · exact g32p_row03_characterBlock_129
  · exact g32p_row03_characterBlock_130
  · exact g32p_row03_characterBlock_131
  · exact g32p_row03_characterBlock_132
  · exact g32p_row03_characterBlock_133
  · exact g32p_row03_characterBlock_134
  · exact g32p_row03_characterBlock_135
  · exact g32p_row03_characterBlock_136
  · exact g32p_row03_characterBlock_137
  · exact g32p_row03_characterBlock_138
  · exact g32p_row03_characterBlock_139
  · exact g32p_row03_characterBlock_140
  · exact g32p_row03_characterBlock_141
  · exact g32p_row03_characterBlock_142
  · exact g32p_row03_characterBlock_143
  · exact g32p_row03_characterBlock_144
  · exact g32p_row03_characterBlock_145
  · exact g32p_row03_characterBlock_146
  · exact g32p_row03_characterBlock_147
  · exact g32p_row03_characterBlock_148
  · exact g32p_row03_characterBlock_149
  · exact g32p_row03_characterBlock_150
  · exact g32p_row03_characterBlock_151
  · exact g32p_row03_characterBlock_152
  · exact g32p_row03_characterBlock_153
  · exact g32p_row03_characterBlock_154
  · exact g32p_row03_characterBlock_155
  · exact g32p_row03_characterBlock_156
  · exact g32p_row03_characterBlock_157
  · exact g32p_row03_characterBlock_158
  · exact g32p_row03_characterBlock_159
  · exact g32p_row03_characterBlock_160
  · exact g32p_row03_characterBlock_161
  · exact g32p_row03_characterBlock_162
  · exact g32p_row03_characterBlock_163
  · exact g32p_row03_characterBlock_164
  · exact g32p_row03_characterBlock_165
  · exact g32p_row03_characterBlock_166
  · exact g32p_row03_characterBlock_167
  · exact g32p_row03_characterBlock_168
  · exact g32p_row03_characterBlock_169
  · exact g32p_row03_characterBlock_170
  · exact g32p_row03_characterBlock_171
  · exact g32p_row03_characterBlock_172
  · exact g32p_row03_characterBlock_173
  · exact g32p_row03_characterBlock_174
  · exact g32p_row03_characterBlock_175
  · exact g32p_row03_characterBlock_176
  · exact g32p_row03_characterBlock_177
  · exact g32p_row03_characterBlock_178
  · exact g32p_row03_characterBlock_179
  · exact g32p_row03_characterBlock_180
  · exact g32p_row03_characterBlock_181
  · exact g32p_row03_characterBlock_182
  · exact g32p_row03_characterBlock_183
  · exact g32p_row03_characterBlock_184
  · exact g32p_row03_characterBlock_185
  · exact g32p_row03_characterBlock_186
  · exact g32p_row03_characterBlock_187
  · exact g32p_row03_characterBlock_188
  · exact g32p_row03_characterBlock_189
  · exact g32p_row03_characterBlock_190
  · exact g32p_row03_characterBlock_191
  · exact g32p_row03_characterBlock_192
  · exact g32p_row03_characterBlock_193
  · exact g32p_row03_characterBlock_194
  · exact g32p_row03_characterBlock_195
  · exact g32p_row03_characterBlock_196
  · exact g32p_row03_characterBlock_197
  · exact g32p_row03_characterBlock_198
  · exact g32p_row03_characterBlock_199
  · exact g32p_row03_characterBlock_200
  · exact g32p_row03_characterBlock_201
  · exact g32p_row03_characterBlock_202
  · exact g32p_row03_characterBlock_203
  · exact g32p_row03_characterBlock_204
  · exact g32p_row03_characterBlock_205
  · exact g32p_row03_characterBlock_206
  · exact g32p_row03_characterBlock_207
  · exact g32p_row03_characterBlock_208
  · exact g32p_row03_characterBlock_209
  · exact g32p_row03_characterBlock_210
  · exact g32p_row03_characterBlock_211
  · exact g32p_row03_characterBlock_212
  · exact g32p_row03_characterBlock_213
  · exact g32p_row03_characterBlock_214
  · exact g32p_row03_characterBlock_215
  · exact g32p_row03_characterBlock_216
  · exact g32p_row03_characterBlock_217
  · exact g32p_row03_characterBlock_218
  · exact g32p_row03_characterBlock_219
  · exact g32p_row03_characterBlock_220
  · exact g32p_row03_characterBlock_221
  · exact g32p_row03_characterBlock_222
  · exact g32p_row03_characterBlock_223
  · exact g32p_row03_characterBlock_224
  · exact g32p_row03_characterBlock_225
  · exact g32p_row03_characterBlock_226
  · exact g32p_row03_characterBlock_227
  · exact g32p_row03_characterBlock_228
  · exact g32p_row03_characterBlock_229
  · exact g32p_row03_characterBlock_230
  · exact g32p_row03_characterBlock_231
  · exact g32p_row03_characterBlock_232
  · exact g32p_row03_characterBlock_233
  · exact g32p_row03_characterBlock_234
  · exact g32p_row03_characterBlock_235
  · exact g32p_row03_characterBlock_236
  · exact g32p_row03_characterBlock_237
  · exact g32p_row03_characterBlock_238
  · exact g32p_row03_characterBlock_239
  · exact g32p_row03_characterBlock_240
  · exact g32p_row03_characterBlock_241
  · exact g32p_row03_characterBlock_242
  · exact g32p_row03_characterBlock_243
  · exact g32p_row03_characterBlock_244
  · exact g32p_row03_characterBlock_245
  · exact g32p_row03_characterBlock_246
  · exact g32p_row03_characterBlock_247
  · exact g32p_row03_characterBlock_248
  · exact g32p_row03_characterBlock_249
  · exact g32p_row03_characterBlock_250
  · exact g32p_row03_characterBlock_251
  · exact g32p_row03_characterBlock_252
  · exact g32p_row03_characterBlock_253
  · exact g32p_row03_characterBlock_254
  · exact g32p_row03_characterBlock_255
  · exact g32p_row03_characterBlock_256
  · exact g32p_row03_characterBlock_257
  · exact g32p_row03_characterBlock_258
  · exact g32p_row03_characterBlock_259
  · exact g32p_row03_characterBlock_260
  · exact g32p_row03_characterBlock_261
  · exact g32p_row03_characterBlock_262
  · exact g32p_row03_characterBlock_263
  · exact g32p_row03_characterBlock_264
  · exact g32p_row03_characterBlock_265
  · exact g32p_row03_characterBlock_266
  · exact g32p_row03_characterBlock_267
  · exact g32p_row03_characterBlock_268
  · exact g32p_row03_characterBlock_269

theorem g32p_row03_characterSurjective : Function.Surjective g32p_row03_characterValues := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
