import HodgeLean.Foundations.Program.G32PropFourSixPacked0189
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixRootPointData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0187

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_08 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 8 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 8 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_128 0
    · exact g32p_rootTransition_check_128 1
    · exact g32p_rootTransition_check_128 2
    · exact g32p_rootTransition_check_128 3
  · fin_cases k
    · exact g32p_rootTransition_check_129 0
    · exact g32p_rootTransition_check_129 1
    · exact g32p_rootTransition_check_129 2
    · exact g32p_rootTransition_check_129 3
  · fin_cases k
    · exact g32p_rootTransition_check_130 0
    · exact g32p_rootTransition_check_130 1
    · exact g32p_rootTransition_check_130 2
    · exact g32p_rootTransition_check_130 3
  · fin_cases k
    · exact g32p_rootTransition_check_131 0
    · exact g32p_rootTransition_check_131 1
    · exact g32p_rootTransition_check_131 2
    · exact g32p_rootTransition_check_131 3
  · fin_cases k
    · exact g32p_rootTransition_check_132 0
    · exact g32p_rootTransition_check_132 1
    · exact g32p_rootTransition_check_132 2
    · exact g32p_rootTransition_check_132 3
  · fin_cases k
    · exact g32p_rootTransition_check_133 0
    · exact g32p_rootTransition_check_133 1
    · exact g32p_rootTransition_check_133 2
    · exact g32p_rootTransition_check_133 3
  · fin_cases k
    · exact g32p_rootTransition_check_134 0
    · exact g32p_rootTransition_check_134 1
    · exact g32p_rootTransition_check_134 2
    · exact g32p_rootTransition_check_134 3
  · fin_cases k
    · exact g32p_rootTransition_check_135 0
    · exact g32p_rootTransition_check_135 1
    · exact g32p_rootTransition_check_135 2
    · exact g32p_rootTransition_check_135 3
  · fin_cases k
    · exact g32p_rootTransition_check_136 0
    · exact g32p_rootTransition_check_136 1
    · exact g32p_rootTransition_check_136 2
    · exact g32p_rootTransition_check_136 3
  · fin_cases k
    · exact g32p_rootTransition_check_137 0
    · exact g32p_rootTransition_check_137 1
    · exact g32p_rootTransition_check_137 2
    · exact g32p_rootTransition_check_137 3
  · fin_cases k
    · exact g32p_rootTransition_check_138 0
    · exact g32p_rootTransition_check_138 1
    · exact g32p_rootTransition_check_138 2
    · exact g32p_rootTransition_check_138 3
  · fin_cases k
    · exact g32p_rootTransition_check_139 0
    · exact g32p_rootTransition_check_139 1
    · exact g32p_rootTransition_check_139 2
    · exact g32p_rootTransition_check_139 3
  · fin_cases k
    · exact g32p_rootTransition_check_140 0
    · exact g32p_rootTransition_check_140 1
    · exact g32p_rootTransition_check_140 2
    · exact g32p_rootTransition_check_140 3
  · fin_cases k
    · exact g32p_rootTransition_check_141 0
    · exact g32p_rootTransition_check_141 1
    · exact g32p_rootTransition_check_141 2
    · exact g32p_rootTransition_check_141 3
  · fin_cases k
    · exact g32p_rootTransition_check_142 0
    · exact g32p_rootTransition_check_142 1
    · exact g32p_rootTransition_check_142 2
    · exact g32p_rootTransition_check_142 3
  · fin_cases k
    · exact g32p_rootTransition_check_143 0
    · exact g32p_rootTransition_check_143 1
    · exact g32p_rootTransition_check_143 2
    · exact g32p_rootTransition_check_143 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_09 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 9 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 9 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_144 0
    · exact g32p_rootTransition_check_144 1
    · exact g32p_rootTransition_check_144 2
    · exact g32p_rootTransition_check_144 3
  · fin_cases k
    · exact g32p_rootTransition_check_145 0
    · exact g32p_rootTransition_check_145 1
    · exact g32p_rootTransition_check_145 2
    · exact g32p_rootTransition_check_145 3
  · fin_cases k
    · exact g32p_rootTransition_check_146 0
    · exact g32p_rootTransition_check_146 1
    · exact g32p_rootTransition_check_146 2
    · exact g32p_rootTransition_check_146 3
  · fin_cases k
    · exact g32p_rootTransition_check_147 0
    · exact g32p_rootTransition_check_147 1
    · exact g32p_rootTransition_check_147 2
    · exact g32p_rootTransition_check_147 3
  · fin_cases k
    · exact g32p_rootTransition_check_148 0
    · exact g32p_rootTransition_check_148 1
    · exact g32p_rootTransition_check_148 2
    · exact g32p_rootTransition_check_148 3
  · fin_cases k
    · exact g32p_rootTransition_check_149 0
    · exact g32p_rootTransition_check_149 1
    · exact g32p_rootTransition_check_149 2
    · exact g32p_rootTransition_check_149 3
  · fin_cases k
    · exact g32p_rootTransition_check_150 0
    · exact g32p_rootTransition_check_150 1
    · exact g32p_rootTransition_check_150 2
    · exact g32p_rootTransition_check_150 3
  · fin_cases k
    · exact g32p_rootTransition_check_151 0
    · exact g32p_rootTransition_check_151 1
    · exact g32p_rootTransition_check_151 2
    · exact g32p_rootTransition_check_151 3
  · fin_cases k
    · exact g32p_rootTransition_check_152 0
    · exact g32p_rootTransition_check_152 1
    · exact g32p_rootTransition_check_152 2
    · exact g32p_rootTransition_check_152 3
  · fin_cases k
    · exact g32p_rootTransition_check_153 0
    · exact g32p_rootTransition_check_153 1
    · exact g32p_rootTransition_check_153 2
    · exact g32p_rootTransition_check_153 3
  · fin_cases k
    · exact g32p_rootTransition_check_154 0
    · exact g32p_rootTransition_check_154 1
    · exact g32p_rootTransition_check_154 2
    · exact g32p_rootTransition_check_154 3
  · fin_cases k
    · exact g32p_rootTransition_check_155 0
    · exact g32p_rootTransition_check_155 1
    · exact g32p_rootTransition_check_155 2
    · exact g32p_rootTransition_check_155 3
  · fin_cases k
    · exact g32p_rootTransition_check_156 0
    · exact g32p_rootTransition_check_156 1
    · exact g32p_rootTransition_check_156 2
    · exact g32p_rootTransition_check_156 3
  · fin_cases k
    · exact g32p_rootTransition_check_157 0
    · exact g32p_rootTransition_check_157 1
    · exact g32p_rootTransition_check_157 2
    · exact g32p_rootTransition_check_157 3
  · fin_cases k
    · exact g32p_rootTransition_check_158 0
    · exact g32p_rootTransition_check_158 1
    · exact g32p_rootTransition_check_158 2
    · exact g32p_rootTransition_check_158 3
  · fin_cases k
    · exact g32p_rootTransition_check_159 0
    · exact g32p_rootTransition_check_159 1
    · exact g32p_rootTransition_check_159 2
    · exact g32p_rootTransition_check_159 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_160 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_160 =
      (![g32p_rootMatrix_160, g32p_rootMatrix_160, g32p_rootMatrix_097, g32p_rootMatrix_159]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_161 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_161 =
      (![g32p_rootMatrix_220, g32p_rootMatrix_044, g32p_rootMatrix_161, g32p_rootMatrix_039]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_162 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_162 =
      (![g32p_rootMatrix_162, g32p_rootMatrix_089, g32p_rootMatrix_162, g32p_rootMatrix_162]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_163 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_163 =
      (![g32p_rootMatrix_206, g32p_rootMatrix_163, g32p_rootMatrix_163, g32p_rootMatrix_040]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_164 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_164 =
      (![g32p_rootMatrix_041, g32p_rootMatrix_164, g32p_rootMatrix_164, g32p_rootMatrix_164]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_165 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_165 =
      (![g32p_rootMatrix_165, g32p_rootMatrix_175, g32p_rootMatrix_092, g32p_rootMatrix_165]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_166 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_166 =
      (![g32p_rootMatrix_166, g32p_rootMatrix_093, g32p_rootMatrix_221, g32p_rootMatrix_047]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_167 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_167 =
      (![g32p_rootMatrix_043, g32p_rootMatrix_167, g32p_rootMatrix_222, g32p_rootMatrix_195]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_168 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_168 =
      (![g32p_rootMatrix_171, g32p_rootMatrix_223, g32p_rootMatrix_168, g32p_rootMatrix_064]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_169 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_169 =
      (![g32p_rootMatrix_222, g32p_rootMatrix_224, g32p_rootMatrix_042, g32p_rootMatrix_225]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_170 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_170 =
      (![g32p_rootMatrix_170, g32p_rootMatrix_064, g32p_rootMatrix_080, g32p_rootMatrix_226]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_171 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_171 =
      (![g32p_rootMatrix_198, g32p_rootMatrix_043, g32p_rootMatrix_171, g32p_rootMatrix_171]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_172 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_172 =
      (![g32p_rootMatrix_172, g32p_rootMatrix_172, g32p_rootMatrix_172, g32p_rootMatrix_100]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_173 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_173 =
      (![g32p_rootMatrix_044, g32p_rootMatrix_173, g32p_rootMatrix_225, g32p_rootMatrix_083]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_174 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_174 =
      (![g32p_rootMatrix_225, g32p_rootMatrix_199, g32p_rootMatrix_141, g32p_rootMatrix_174]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_175 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_175 =
      (![g32p_rootMatrix_141, g32p_rootMatrix_227, g32p_rootMatrix_044, g32p_rootMatrix_175]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_176 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_176 =
      (![g32p_rootMatrix_050, g32p_rootMatrix_176, g32p_rootMatrix_045, g32p_rootMatrix_146]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_177 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_177 =
      (![g32p_rootMatrix_177, g32p_rootMatrix_177, g32p_rootMatrix_147, g32p_rootMatrix_176]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_178 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_178 =
      (![g32p_rootMatrix_069, g32p_rootMatrix_046, g32p_rootMatrix_066, g32p_rootMatrix_224]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_179 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_179 =
      (![g32p_rootMatrix_048, g32p_rootMatrix_080, g32p_rootMatrix_215, g32p_rootMatrix_228]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_10 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 10 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 10 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_160 0
    · exact g32p_rootTransition_check_160 1
    · exact g32p_rootTransition_check_160 2
    · exact g32p_rootTransition_check_160 3
  · fin_cases k
    · exact g32p_rootTransition_check_161 0
    · exact g32p_rootTransition_check_161 1
    · exact g32p_rootTransition_check_161 2
    · exact g32p_rootTransition_check_161 3
  · fin_cases k
    · exact g32p_rootTransition_check_162 0
    · exact g32p_rootTransition_check_162 1
    · exact g32p_rootTransition_check_162 2
    · exact g32p_rootTransition_check_162 3
  · fin_cases k
    · exact g32p_rootTransition_check_163 0
    · exact g32p_rootTransition_check_163 1
    · exact g32p_rootTransition_check_163 2
    · exact g32p_rootTransition_check_163 3
  · fin_cases k
    · exact g32p_rootTransition_check_164 0
    · exact g32p_rootTransition_check_164 1
    · exact g32p_rootTransition_check_164 2
    · exact g32p_rootTransition_check_164 3
  · fin_cases k
    · exact g32p_rootTransition_check_165 0
    · exact g32p_rootTransition_check_165 1
    · exact g32p_rootTransition_check_165 2
    · exact g32p_rootTransition_check_165 3
  · fin_cases k
    · exact g32p_rootTransition_check_166 0
    · exact g32p_rootTransition_check_166 1
    · exact g32p_rootTransition_check_166 2
    · exact g32p_rootTransition_check_166 3
  · fin_cases k
    · exact g32p_rootTransition_check_167 0
    · exact g32p_rootTransition_check_167 1
    · exact g32p_rootTransition_check_167 2
    · exact g32p_rootTransition_check_167 3
  · fin_cases k
    · exact g32p_rootTransition_check_168 0
    · exact g32p_rootTransition_check_168 1
    · exact g32p_rootTransition_check_168 2
    · exact g32p_rootTransition_check_168 3
  · fin_cases k
    · exact g32p_rootTransition_check_169 0
    · exact g32p_rootTransition_check_169 1
    · exact g32p_rootTransition_check_169 2
    · exact g32p_rootTransition_check_169 3
  · fin_cases k
    · exact g32p_rootTransition_check_170 0
    · exact g32p_rootTransition_check_170 1
    · exact g32p_rootTransition_check_170 2
    · exact g32p_rootTransition_check_170 3
  · fin_cases k
    · exact g32p_rootTransition_check_171 0
    · exact g32p_rootTransition_check_171 1
    · exact g32p_rootTransition_check_171 2
    · exact g32p_rootTransition_check_171 3
  · fin_cases k
    · exact g32p_rootTransition_check_172 0
    · exact g32p_rootTransition_check_172 1
    · exact g32p_rootTransition_check_172 2
    · exact g32p_rootTransition_check_172 3
  · fin_cases k
    · exact g32p_rootTransition_check_173 0
    · exact g32p_rootTransition_check_173 1
    · exact g32p_rootTransition_check_173 2
    · exact g32p_rootTransition_check_173 3
  · fin_cases k
    · exact g32p_rootTransition_check_174 0
    · exact g32p_rootTransition_check_174 1
    · exact g32p_rootTransition_check_174 2
    · exact g32p_rootTransition_check_174 3
  · fin_cases k
    · exact g32p_rootTransition_check_175 0
    · exact g32p_rootTransition_check_175 1
    · exact g32p_rootTransition_check_175 2
    · exact g32p_rootTransition_check_175 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_180 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_180 =
      (![g32p_rootMatrix_180, g32p_rootMatrix_228, g32p_rootMatrix_181, g32p_rootMatrix_078]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_181 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_181 =
      (![g32p_rootMatrix_181, g32p_rootMatrix_225, g32p_rootMatrix_229, g32p_rootMatrix_046]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_182 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_182 =
      (![g32p_rootMatrix_215, g32p_rootMatrix_230, g32p_rootMatrix_047, g32p_rootMatrix_182]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_183 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_183 =
      (![g32p_rootMatrix_183, g32p_rootMatrix_183, g32p_rootMatrix_166, g32p_rootMatrix_231]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_184 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_184 =
      (![g32p_rootMatrix_209, g32p_rootMatrix_184, g32p_rootMatrix_184, g32p_rootMatrix_111]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_185 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_185 =
      (![g32p_rootMatrix_109, g32p_rootMatrix_185, g32p_rootMatrix_185, g32p_rootMatrix_185]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_186 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_186 =
      (![g32p_rootMatrix_106, g32p_rootMatrix_221, g32p_rootMatrix_186, g32p_rootMatrix_186]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_187 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_187 =
      (![g32p_rootMatrix_187, g32p_rootMatrix_188, g32p_rootMatrix_135, g32p_rootMatrix_187]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_188 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_188 =
      (![g32p_rootMatrix_057, g32p_rootMatrix_138, g32p_rootMatrix_054, g32p_rootMatrix_188]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_189 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_189 =
      (![g32p_rootMatrix_189, g32p_rootMatrix_055, g32p_rootMatrix_232, g32p_rootMatrix_216]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_190 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_190 =
      (![g32p_rootMatrix_190, g32p_rootMatrix_065, g32p_rootMatrix_189, g32p_rootMatrix_233]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_191 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_191 =
      (![g32p_rootMatrix_059, g32p_rootMatrix_233, g32p_rootMatrix_226, g32p_rootMatrix_063]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_192 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_192 =
      (![g32p_rootMatrix_085, g32p_rootMatrix_217, g32p_rootMatrix_083, g32p_rootMatrix_055]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_193 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_193 =
      (![g32p_rootMatrix_119, g32p_rootMatrix_193, g32p_rootMatrix_193, g32p_rootMatrix_214]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_194 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_194 =
      (![g32p_rootMatrix_194, g32p_rootMatrix_234, g32p_rootMatrix_152, g32p_rootMatrix_194]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_195 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_195 =
      (![g32p_rootMatrix_226, g32p_rootMatrix_195, g32p_rootMatrix_058, g32p_rootMatrix_235]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_196 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_196 =
      (![g32p_rootMatrix_200, g32p_rootMatrix_116, g32p_rootMatrix_196, g32p_rootMatrix_196]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_197 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_197 =
      (![g32p_rootMatrix_197, g32p_rootMatrix_061, g32p_rootMatrix_197, g32p_rootMatrix_197]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_198 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_198 =
      (![g32p_rootMatrix_168, g32p_rootMatrix_198, g32p_rootMatrix_198, g32p_rootMatrix_129]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_199 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_199 =
      (![g32p_rootMatrix_199, g32p_rootMatrix_236, g32p_rootMatrix_062, g32p_rootMatrix_199]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_11 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 11 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 11 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_176 0
    · exact g32p_rootTransition_check_176 1
    · exact g32p_rootTransition_check_176 2
    · exact g32p_rootTransition_check_176 3
  · fin_cases k
    · exact g32p_rootTransition_check_177 0
    · exact g32p_rootTransition_check_177 1
    · exact g32p_rootTransition_check_177 2
    · exact g32p_rootTransition_check_177 3
  · fin_cases k
    · exact g32p_rootTransition_check_178 0
    · exact g32p_rootTransition_check_178 1
    · exact g32p_rootTransition_check_178 2
    · exact g32p_rootTransition_check_178 3
  · fin_cases k
    · exact g32p_rootTransition_check_179 0
    · exact g32p_rootTransition_check_179 1
    · exact g32p_rootTransition_check_179 2
    · exact g32p_rootTransition_check_179 3
  · fin_cases k
    · exact g32p_rootTransition_check_180 0
    · exact g32p_rootTransition_check_180 1
    · exact g32p_rootTransition_check_180 2
    · exact g32p_rootTransition_check_180 3
  · fin_cases k
    · exact g32p_rootTransition_check_181 0
    · exact g32p_rootTransition_check_181 1
    · exact g32p_rootTransition_check_181 2
    · exact g32p_rootTransition_check_181 3
  · fin_cases k
    · exact g32p_rootTransition_check_182 0
    · exact g32p_rootTransition_check_182 1
    · exact g32p_rootTransition_check_182 2
    · exact g32p_rootTransition_check_182 3
  · fin_cases k
    · exact g32p_rootTransition_check_183 0
    · exact g32p_rootTransition_check_183 1
    · exact g32p_rootTransition_check_183 2
    · exact g32p_rootTransition_check_183 3
  · fin_cases k
    · exact g32p_rootTransition_check_184 0
    · exact g32p_rootTransition_check_184 1
    · exact g32p_rootTransition_check_184 2
    · exact g32p_rootTransition_check_184 3
  · fin_cases k
    · exact g32p_rootTransition_check_185 0
    · exact g32p_rootTransition_check_185 1
    · exact g32p_rootTransition_check_185 2
    · exact g32p_rootTransition_check_185 3
  · fin_cases k
    · exact g32p_rootTransition_check_186 0
    · exact g32p_rootTransition_check_186 1
    · exact g32p_rootTransition_check_186 2
    · exact g32p_rootTransition_check_186 3
  · fin_cases k
    · exact g32p_rootTransition_check_187 0
    · exact g32p_rootTransition_check_187 1
    · exact g32p_rootTransition_check_187 2
    · exact g32p_rootTransition_check_187 3
  · fin_cases k
    · exact g32p_rootTransition_check_188 0
    · exact g32p_rootTransition_check_188 1
    · exact g32p_rootTransition_check_188 2
    · exact g32p_rootTransition_check_188 3
  · fin_cases k
    · exact g32p_rootTransition_check_189 0
    · exact g32p_rootTransition_check_189 1
    · exact g32p_rootTransition_check_189 2
    · exact g32p_rootTransition_check_189 3
  · fin_cases k
    · exact g32p_rootTransition_check_190 0
    · exact g32p_rootTransition_check_190 1
    · exact g32p_rootTransition_check_190 2
    · exact g32p_rootTransition_check_190 3
  · fin_cases k
    · exact g32p_rootTransition_check_191 0
    · exact g32p_rootTransition_check_191 1
    · exact g32p_rootTransition_check_191 2
    · exact g32p_rootTransition_check_191 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_200 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_200 =
      (![g32p_rootMatrix_203, g32p_rootMatrix_226, g32p_rootMatrix_200, g32p_rootMatrix_223]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_201 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_201 =
      (![g32p_rootMatrix_201, g32p_rootMatrix_201, g32p_rootMatrix_132, g32p_rootMatrix_201]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_202 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_202 =
      (![g32p_rootMatrix_202, g32p_rootMatrix_102, g32p_rootMatrix_202, g32p_rootMatrix_202]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_203 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_203 =
      (![g32p_rootMatrix_196, g32p_rootMatrix_203, g32p_rootMatrix_203, g32p_rootMatrix_067]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_204 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_204 =
      (![g32p_rootMatrix_236, g32p_rootMatrix_181, g32p_rootMatrix_204, g32p_rootMatrix_178]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_205 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_205 =
      (![g32p_rootMatrix_205, g32p_rootMatrix_205, g32p_rootMatrix_076, g32p_rootMatrix_237]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_206 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_206 =
      (![g32p_rootMatrix_155, g32p_rootMatrix_139, g32p_rootMatrix_206, g32p_rootMatrix_206]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_207 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_207 =
      (![g32p_rootMatrix_207, g32p_rootMatrix_207, g32p_rootMatrix_207, g32p_rootMatrix_077]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_208 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_208 =
      (![g32p_rootMatrix_208, g32p_rootMatrix_208, g32p_rootMatrix_143, g32p_rootMatrix_208]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_209 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_209 =
      (![g32p_rootMatrix_210, g32p_rootMatrix_218, g32p_rootMatrix_209, g32p_rootMatrix_215]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_210 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_210 =
      (![g32p_rootMatrix_184, g32p_rootMatrix_084, g32p_rootMatrix_210, g32p_rootMatrix_210]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_211 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_211 =
      (![g32p_rootMatrix_211, g32p_rootMatrix_211, g32p_rootMatrix_211, g32p_rootMatrix_118]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_212 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_212 =
      (![g32p_rootMatrix_237, g32p_rootMatrix_192, g32p_rootMatrix_212, g32p_rootMatrix_189]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_213 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_213 =
      (![g32p_rootMatrix_091, g32p_rootMatrix_213, g32p_rootMatrix_086, g32p_rootMatrix_193]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_214 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_214 =
      (![g32p_rootMatrix_214, g32p_rootMatrix_214, g32p_rootMatrix_194, g32p_rootMatrix_213]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_215 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_215 =
      (![g32p_rootMatrix_110, g32p_rootMatrix_087, g32p_rootMatrix_107, g32p_rootMatrix_143]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_216 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_216 =
      (![g32p_rootMatrix_089, g32p_rootMatrix_121, g32p_rootMatrix_130, g32p_rootMatrix_212]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_217 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_217 =
      (![g32p_rootMatrix_217, g32p_rootMatrix_212, g32p_rootMatrix_218, g32p_rootMatrix_119]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_218 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_218 =
      (![g32p_rootMatrix_218, g32p_rootMatrix_144, g32p_rootMatrix_238, g32p_rootMatrix_087]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_219 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_219 =
      (![g32p_rootMatrix_233, g32p_rootMatrix_219, g32p_rootMatrix_219, g32p_rootMatrix_160]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_12 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 12 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 12 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_192 0
    · exact g32p_rootTransition_check_192 1
    · exact g32p_rootTransition_check_192 2
    · exact g32p_rootTransition_check_192 3
  · fin_cases k
    · exact g32p_rootTransition_check_193 0
    · exact g32p_rootTransition_check_193 1
    · exact g32p_rootTransition_check_193 2
    · exact g32p_rootTransition_check_193 3
  · fin_cases k
    · exact g32p_rootTransition_check_194 0
    · exact g32p_rootTransition_check_194 1
    · exact g32p_rootTransition_check_194 2
    · exact g32p_rootTransition_check_194 3
  · fin_cases k
    · exact g32p_rootTransition_check_195 0
    · exact g32p_rootTransition_check_195 1
    · exact g32p_rootTransition_check_195 2
    · exact g32p_rootTransition_check_195 3
  · fin_cases k
    · exact g32p_rootTransition_check_196 0
    · exact g32p_rootTransition_check_196 1
    · exact g32p_rootTransition_check_196 2
    · exact g32p_rootTransition_check_196 3
  · fin_cases k
    · exact g32p_rootTransition_check_197 0
    · exact g32p_rootTransition_check_197 1
    · exact g32p_rootTransition_check_197 2
    · exact g32p_rootTransition_check_197 3
  · fin_cases k
    · exact g32p_rootTransition_check_198 0
    · exact g32p_rootTransition_check_198 1
    · exact g32p_rootTransition_check_198 2
    · exact g32p_rootTransition_check_198 3
  · fin_cases k
    · exact g32p_rootTransition_check_199 0
    · exact g32p_rootTransition_check_199 1
    · exact g32p_rootTransition_check_199 2
    · exact g32p_rootTransition_check_199 3
  · fin_cases k
    · exact g32p_rootTransition_check_200 0
    · exact g32p_rootTransition_check_200 1
    · exact g32p_rootTransition_check_200 2
    · exact g32p_rootTransition_check_200 3
  · fin_cases k
    · exact g32p_rootTransition_check_201 0
    · exact g32p_rootTransition_check_201 1
    · exact g32p_rootTransition_check_201 2
    · exact g32p_rootTransition_check_201 3
  · fin_cases k
    · exact g32p_rootTransition_check_202 0
    · exact g32p_rootTransition_check_202 1
    · exact g32p_rootTransition_check_202 2
    · exact g32p_rootTransition_check_202 3
  · fin_cases k
    · exact g32p_rootTransition_check_203 0
    · exact g32p_rootTransition_check_203 1
    · exact g32p_rootTransition_check_203 2
    · exact g32p_rootTransition_check_203 3
  · fin_cases k
    · exact g32p_rootTransition_check_204 0
    · exact g32p_rootTransition_check_204 1
    · exact g32p_rootTransition_check_204 2
    · exact g32p_rootTransition_check_204 3
  · fin_cases k
    · exact g32p_rootTransition_check_205 0
    · exact g32p_rootTransition_check_205 1
    · exact g32p_rootTransition_check_205 2
    · exact g32p_rootTransition_check_205 3
  · fin_cases k
    · exact g32p_rootTransition_check_206 0
    · exact g32p_rootTransition_check_206 1
    · exact g32p_rootTransition_check_206 2
    · exact g32p_rootTransition_check_206 3
  · fin_cases k
    · exact g32p_rootTransition_check_207 0
    · exact g32p_rootTransition_check_207 1
    · exact g32p_rootTransition_check_207 2
    · exact g32p_rootTransition_check_207 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_220 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_220 =
      (![g32p_rootMatrix_158, g32p_rootMatrix_220, g32p_rootMatrix_220, g32p_rootMatrix_220]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_221 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_221 =
      (![g32p_rootMatrix_221, g32p_rootMatrix_222, g32p_rootMatrix_183, g32p_rootMatrix_221]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_222 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_222 =
      (![g32p_rootMatrix_098, g32p_rootMatrix_186, g32p_rootMatrix_095, g32p_rootMatrix_222]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_223 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_223 =
      (![g32p_rootMatrix_223, g32p_rootMatrix_096, g32p_rootMatrix_239, g32p_rootMatrix_131]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_224 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_224 =
      (![g32p_rootMatrix_224, g32p_rootMatrix_106, g32p_rootMatrix_223, g32p_rootMatrix_204]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_225 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_225 =
      (![g32p_rootMatrix_100, g32p_rootMatrix_204, g32p_rootMatrix_145, g32p_rootMatrix_104]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_226 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_226 =
      (![g32p_rootMatrix_126, g32p_rootMatrix_132, g32p_rootMatrix_124, g32p_rootMatrix_096]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_227 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_227 =
      (![g32p_rootMatrix_228, g32p_rootMatrix_165, g32p_rootMatrix_227, g32p_rootMatrix_227]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_228 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_228 =
      (![g32p_rootMatrix_231, g32p_rootMatrix_145, g32p_rootMatrix_228, g32p_rootMatrix_142]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_229 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_229 =
      (![g32p_rootMatrix_229, g32p_rootMatrix_229, g32p_rootMatrix_180, g32p_rootMatrix_229]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_230 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_230 =
      (![g32p_rootMatrix_230, g32p_rootMatrix_151, g32p_rootMatrix_230, g32p_rootMatrix_230]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_231 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_231 =
      (![g32p_rootMatrix_227, g32p_rootMatrix_231, g32p_rootMatrix_231, g32p_rootMatrix_108]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_232 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_232 =
      (![g32p_rootMatrix_232, g32p_rootMatrix_232, g32p_rootMatrix_190, g32p_rootMatrix_232]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_233 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_233 =
      (![g32p_rootMatrix_234, g32p_rootMatrix_133, g32p_rootMatrix_233, g32p_rootMatrix_130]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_234 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_234 =
      (![g32p_rootMatrix_219, g32p_rootMatrix_125, g32p_rootMatrix_234, g32p_rootMatrix_234]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_235 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_235 =
      (![g32p_rootMatrix_235, g32p_rootMatrix_235, g32p_rootMatrix_235, g32p_rootMatrix_167]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_236 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_236 =
      (![g32p_rootMatrix_136, g32p_rootMatrix_174, g32p_rootMatrix_236, g32p_rootMatrix_236]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_237 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_237 =
      (![g32p_rootMatrix_149, g32p_rootMatrix_237, g32p_rootMatrix_237, g32p_rootMatrix_157]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_238 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_238 =
      (![g32p_rootMatrix_238, g32p_rootMatrix_238, g32p_rootMatrix_217, g32p_rootMatrix_238]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_239 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_239 =
      (![g32p_rootMatrix_239, g32p_rootMatrix_239, g32p_rootMatrix_224, g32p_rootMatrix_239]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_13 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 13 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 13 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_208 0
    · exact g32p_rootTransition_check_208 1
    · exact g32p_rootTransition_check_208 2
    · exact g32p_rootTransition_check_208 3
  · fin_cases k
    · exact g32p_rootTransition_check_209 0
    · exact g32p_rootTransition_check_209 1
    · exact g32p_rootTransition_check_209 2
    · exact g32p_rootTransition_check_209 3
  · fin_cases k
    · exact g32p_rootTransition_check_210 0
    · exact g32p_rootTransition_check_210 1
    · exact g32p_rootTransition_check_210 2
    · exact g32p_rootTransition_check_210 3
  · fin_cases k
    · exact g32p_rootTransition_check_211 0
    · exact g32p_rootTransition_check_211 1
    · exact g32p_rootTransition_check_211 2
    · exact g32p_rootTransition_check_211 3
  · fin_cases k
    · exact g32p_rootTransition_check_212 0
    · exact g32p_rootTransition_check_212 1
    · exact g32p_rootTransition_check_212 2
    · exact g32p_rootTransition_check_212 3
  · fin_cases k
    · exact g32p_rootTransition_check_213 0
    · exact g32p_rootTransition_check_213 1
    · exact g32p_rootTransition_check_213 2
    · exact g32p_rootTransition_check_213 3
  · fin_cases k
    · exact g32p_rootTransition_check_214 0
    · exact g32p_rootTransition_check_214 1
    · exact g32p_rootTransition_check_214 2
    · exact g32p_rootTransition_check_214 3
  · fin_cases k
    · exact g32p_rootTransition_check_215 0
    · exact g32p_rootTransition_check_215 1
    · exact g32p_rootTransition_check_215 2
    · exact g32p_rootTransition_check_215 3
  · fin_cases k
    · exact g32p_rootTransition_check_216 0
    · exact g32p_rootTransition_check_216 1
    · exact g32p_rootTransition_check_216 2
    · exact g32p_rootTransition_check_216 3
  · fin_cases k
    · exact g32p_rootTransition_check_217 0
    · exact g32p_rootTransition_check_217 1
    · exact g32p_rootTransition_check_217 2
    · exact g32p_rootTransition_check_217 3
  · fin_cases k
    · exact g32p_rootTransition_check_218 0
    · exact g32p_rootTransition_check_218 1
    · exact g32p_rootTransition_check_218 2
    · exact g32p_rootTransition_check_218 3
  · fin_cases k
    · exact g32p_rootTransition_check_219 0
    · exact g32p_rootTransition_check_219 1
    · exact g32p_rootTransition_check_219 2
    · exact g32p_rootTransition_check_219 3
  · fin_cases k
    · exact g32p_rootTransition_check_220 0
    · exact g32p_rootTransition_check_220 1
    · exact g32p_rootTransition_check_220 2
    · exact g32p_rootTransition_check_220 3
  · fin_cases k
    · exact g32p_rootTransition_check_221 0
    · exact g32p_rootTransition_check_221 1
    · exact g32p_rootTransition_check_221 2
    · exact g32p_rootTransition_check_221 3
  · fin_cases k
    · exact g32p_rootTransition_check_222 0
    · exact g32p_rootTransition_check_222 1
    · exact g32p_rootTransition_check_222 2
    · exact g32p_rootTransition_check_222 3
  · fin_cases k
    · exact g32p_rootTransition_check_223 0
    · exact g32p_rootTransition_check_223 1
    · exact g32p_rootTransition_check_223 2
    · exact g32p_rootTransition_check_223 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_14 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 14 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 14 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_224 0
    · exact g32p_rootTransition_check_224 1
    · exact g32p_rootTransition_check_224 2
    · exact g32p_rootTransition_check_224 3
  · fin_cases k
    · exact g32p_rootTransition_check_225 0
    · exact g32p_rootTransition_check_225 1
    · exact g32p_rootTransition_check_225 2
    · exact g32p_rootTransition_check_225 3
  · fin_cases k
    · exact g32p_rootTransition_check_226 0
    · exact g32p_rootTransition_check_226 1
    · exact g32p_rootTransition_check_226 2
    · exact g32p_rootTransition_check_226 3
  · fin_cases k
    · exact g32p_rootTransition_check_227 0
    · exact g32p_rootTransition_check_227 1
    · exact g32p_rootTransition_check_227 2
    · exact g32p_rootTransition_check_227 3
  · fin_cases k
    · exact g32p_rootTransition_check_228 0
    · exact g32p_rootTransition_check_228 1
    · exact g32p_rootTransition_check_228 2
    · exact g32p_rootTransition_check_228 3
  · fin_cases k
    · exact g32p_rootTransition_check_229 0
    · exact g32p_rootTransition_check_229 1
    · exact g32p_rootTransition_check_229 2
    · exact g32p_rootTransition_check_229 3
  · fin_cases k
    · exact g32p_rootTransition_check_230 0
    · exact g32p_rootTransition_check_230 1
    · exact g32p_rootTransition_check_230 2
    · exact g32p_rootTransition_check_230 3
  · fin_cases k
    · exact g32p_rootTransition_check_231 0
    · exact g32p_rootTransition_check_231 1
    · exact g32p_rootTransition_check_231 2
    · exact g32p_rootTransition_check_231 3
  · fin_cases k
    · exact g32p_rootTransition_check_232 0
    · exact g32p_rootTransition_check_232 1
    · exact g32p_rootTransition_check_232 2
    · exact g32p_rootTransition_check_232 3
  · fin_cases k
    · exact g32p_rootTransition_check_233 0
    · exact g32p_rootTransition_check_233 1
    · exact g32p_rootTransition_check_233 2
    · exact g32p_rootTransition_check_233 3
  · fin_cases k
    · exact g32p_rootTransition_check_234 0
    · exact g32p_rootTransition_check_234 1
    · exact g32p_rootTransition_check_234 2
    · exact g32p_rootTransition_check_234 3
  · fin_cases k
    · exact g32p_rootTransition_check_235 0
    · exact g32p_rootTransition_check_235 1
    · exact g32p_rootTransition_check_235 2
    · exact g32p_rootTransition_check_235 3
  · fin_cases k
    · exact g32p_rootTransition_check_236 0
    · exact g32p_rootTransition_check_236 1
    · exact g32p_rootTransition_check_236 2
    · exact g32p_rootTransition_check_236 3
  · fin_cases k
    · exact g32p_rootTransition_check_237 0
    · exact g32p_rootTransition_check_237 1
    · exact g32p_rootTransition_check_237 2
    · exact g32p_rootTransition_check_237 3
  · fin_cases k
    · exact g32p_rootTransition_check_238 0
    · exact g32p_rootTransition_check_238 1
    · exact g32p_rootTransition_check_238 2
    · exact g32p_rootTransition_check_238 3
  · fin_cases k
    · exact g32p_rootTransition_check_239 0
    · exact g32p_rootTransition_check_239 1
    · exact g32p_rootTransition_check_239 2
    · exact g32p_rootTransition_check_239 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check (i : Fin 240) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) (g32p_rootMatrix i) =
      g32p_rootMatrix (g32p_rootTransition i k) := by
  apply g32p_forall_fin_blocks (fun i =>
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) (g32p_rootMatrix i) =
      g32p_rootMatrix (g32p_rootTransition i k)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_rootTransition_block_00 r k
  · exact g32p_rootTransition_block_01 r k
  · exact g32p_rootTransition_block_02 r k
  · exact g32p_rootTransition_block_03 r k
  · exact g32p_rootTransition_block_04 r k
  · exact g32p_rootTransition_block_05 r k
  · exact g32p_rootTransition_block_06 r k
  · exact g32p_rootTransition_block_07 r k
  · exact g32p_rootTransition_block_08 r k
  · exact g32p_rootTransition_block_09 r k
  · exact g32p_rootTransition_block_10 r k
  · exact g32p_rootTransition_block_11 r k
  · exact g32p_rootTransition_block_12 r k
  · exact g32p_rootTransition_block_13 r k
  · exact g32p_rootTransition_block_14 r k

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

def g32p_rootPoint (i : Fin 240) : Matrix (Fin 4) (Fin 4) ℂ :=
  HurwitzPrymRex_g32P * HurwitzPrymRex_evM g32h_omega (g32p_rootMatrix i)

theorem g32p_rootPoint_finite : (Set.range g32p_rootPoint).Finite :=
  Set.finite_range _

theorem g32p_rootPoint_transport (M V : HurwitzPrymRex_Mat) :
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega M) *
        (HurwitzPrymRex_g32P * HurwitzPrymRex_evM g32h_omega V) =
      HurwitzPrymRex_g32P * HurwitzPrymRex_evM g32h_omega (HurwitzPrymRex_mmul M V) := by
  rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  change (HurwitzPrymRex_g32P * _ * HurwitzPrymRex_g32Pinv) *
    (HurwitzPrymRex_g32P * _) = _
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc HurwitzPrymRex_g32Pinv
    HurwitzPrymRex_g32P, HurwitzPrymRex_g32_Pinv_P, Matrix.one_mul]

theorem g32p_rootPoint_generator (k : Fin 4) (i : Fin 240) :
    (g32p_archiveGenerators k).submatrix g32p_archiveCoordinates
      g32p_archiveCoordinates * g32p_rootPoint i =
        g32p_rootPoint (g32p_rootTransition i k) := by
  rw [← g32p_archiveGenerator_word, g32p_integralWord_map, g32p_archiveWordIntegral]
  exact (g32p_rootPoint_transport _ _).trans
    (congrArg (fun V => HurwitzPrymRex_g32P * HurwitzPrymRex_evM g32h_omega V)
      (g32p_rootTransition_check i k))

theorem g32p_rootPoint_invariant (g : g32p_G) (x : Matrix (Fin 4) (Fin 4) ℂ)
    (hx : x ∈ Set.range g32p_rootPoint) :
    b4b_toMatrix g * x ∈ Set.range g32p_rootPoint := by
  apply g32p_matrix_invariant_of_archive _ _ g x hx
  intro k x hx
  obtain ⟨i, rfl⟩ := hx
  exact ⟨g32p_rootTransition i k, (g32p_rootPoint_generator k i).symm⟩

theorem g32p_rootPoint_eigen_iff (c : Fin 102) (i : Fin 240) (z : HurwitzPrymRex_Zw) :
    b4b_toMatrix (g32p_literalRepresentative c) * g32p_rootPoint i =
        HurwitzPrymRex_ev g32h_omega z • g32p_rootPoint i ↔
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix c) (g32p_rootMatrix i) =
        (fun r s => HurwitzPrymRex_Zw.mul z (g32p_rootMatrix i r s)) := by
  rw [g32p_literalRepresentative_matrix, g32p_rootPoint, g32p_rootPoint_transport]
  have hscale : HurwitzPrymRex_evM g32h_omega
      (fun r s => HurwitzPrymRex_Zw.mul z (g32p_rootMatrix i r s)) =
      HurwitzPrymRex_ev g32h_omega z • HurwitzPrymRex_evM g32h_omega (g32p_rootMatrix i) := by
    ext r s
    exact HurwitzPrymRex_ev_mul g32h_omega_sq_add _ _
  rw [← Matrix.mul_smul, ← hscale]
  constructor
  · intro h
    apply HurwitzPrymRex_evM_injective g32h_omega_sq_add
    have hh := congrArg (fun M => HurwitzPrymRex_g32Pinv * M) h
    simpa only [← Matrix.mul_assoc, HurwitzPrymRex_g32_Pinv_P, Matrix.one_mul] using hh
  · intro h
    rw [h]

end HodgeLean.Foundations.Program

end
end
