import HodgeLean.Foundations.Program.G32PropFourSixPacked0192
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0191
import HodgeLean.Foundations.Program.G32PropFourSixPacked0187
import HodgeLean.Foundations.Program.G32PropFourSixRootPointData

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_determinantTrace_arithmetic_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_literalTraceValue (g32p_determinantTraceRowIndex k) (g32p_finBlockIndex 102 0 r) =
      g32p_determinantTracePair (g32p_finBlockIndex 102 0 r) k := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_determinantTrace_arithmetic_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_literalTraceValue (g32p_determinantTraceRowIndex k) (g32p_finBlockIndex 102 1 r) =
      g32p_determinantTracePair (g32p_finBlockIndex 102 1 r) k := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_determinantTrace_arithmetic_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_literalTraceValue (g32p_determinantTraceRowIndex k) (g32p_finBlockIndex 102 2 r) =
      g32p_determinantTracePair (g32p_finBlockIndex 102 2 r) k := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_determinantTrace_arithmetic_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_literalTraceValue (g32p_determinantTraceRowIndex k) (g32p_finBlockIndex 102 3 r) =
      g32p_determinantTracePair (g32p_finBlockIndex 102 3 r) k := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_determinantTrace_arithmetic_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_literalTraceValue (g32p_determinantTraceRowIndex k) (g32p_finBlockIndex 102 4 r) =
      g32p_determinantTracePair (g32p_finBlockIndex 102 4 r) k := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_determinantTrace_arithmetic_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_literalTraceValue (g32p_determinantTraceRowIndex k) (g32p_finBlockIndex 102 5 r) =
      g32p_determinantTracePair (g32p_finBlockIndex 102 5 r) k := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_determinantTrace_arithmetic_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_literalTraceValue (g32p_determinantTraceRowIndex k) (g32p_finBlockIndex 102 6 r) =
      g32p_determinantTracePair (g32p_finBlockIndex 102 6 r) k := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_determinantTrace_arithmetic (c : Fin 102) (k : Fin 8) :
    g32p_literalTraceValue (g32p_determinantTraceRowIndex k) c =
      g32p_determinantTracePair c k := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_determinantTraceRowIndex k) c =
      g32p_determinantTracePair c k) ?_ c
  intro q r
  fin_cases q
  · exact g32p_determinantTrace_arithmetic_block_00 r k
  · exact g32p_determinantTrace_arithmetic_block_01 r k
  · exact g32p_determinantTrace_arithmetic_block_02 r k
  · exact g32p_determinantTrace_arithmetic_block_03 r k
  · exact g32p_determinantTrace_arithmetic_block_04 r k
  · exact g32p_determinantTrace_arithmetic_block_05 r k
  · exact g32p_determinantTrace_arithmetic_block_06 r k

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32p_determinant_inverse_square (g : g32p_G) :
    (g32p_determinant g : ℂ)⁻¹ = (g32p_determinant g : ℂ) ^ 2 := by
  have h : (g32p_determinant g)⁻¹ = (g32p_determinant g) ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', g32p_determinant_cube]
  simpa only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val] using
    congrArg (fun u : ℂˣ => (u : ℂ)) h

theorem g32p_determinantTracePair_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_determinantTraceRowIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_determinantTracePair c k) := by
  have hd := g32p_literalDeterminantPair_eval c
  have ht := (g32p_literalPowerTrace_actual c 0).symm
  have hcube : (g32p_determinant (g32p_literalRepresentative c) : ℂ) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u : ℂˣ => (u : ℂ))
        (g32p_determinant_cube (g32p_literalRepresentative c))
  have hone : HurwitzPrymRex_ev g32h_omega ⟨1, 0⟩ = 1 := by
    norm_num [HurwitzPrymRex_ev]
  fin_cases k
  · change (g32p_inductionGenerator 0 false 0).character
        (g32p_literalRepresentative c) = _
    rw [g32p_determinantSupplier_generator_character]
    simp [g32p_determinantTracePair, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hd, ht, hone, g32p_determinant_inverse_square] <;> ring_nf <;> first
    | exact hcube
    | linear_combination (g32p_determinant (g32p_literalRepresentative c) : ℂ) * hcube
  · change (g32p_inductionGenerator 0 true 0).character
        (g32p_literalRepresentative c) = _
    rw [g32p_determinantSupplier_generator_character]
    simp [g32p_determinantTracePair, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hd, ht, hone, g32p_determinant_inverse_square] <;> ring_nf <;> first
    | exact hcube
    | linear_combination (g32p_determinant (g32p_literalRepresentative c) : ℂ) * hcube
  · change (g32p_inductionGenerator 0 false 1).character
        (g32p_literalRepresentative c) = _
    rw [g32p_determinantSupplier_generator_character]
    simp [g32p_determinantTracePair, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hd, ht, hone, g32p_determinant_inverse_square] <;> ring_nf <;> first
    | exact hcube
    | linear_combination (g32p_determinant (g32p_literalRepresentative c) : ℂ) * hcube
  · change (g32p_inductionGenerator 0 true 1).character
        (g32p_literalRepresentative c) = _
    rw [g32p_determinantSupplier_generator_character]
    simp [g32p_determinantTracePair, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hd, ht, hone, g32p_determinant_inverse_square] <;> ring_nf <;> first
    | exact hcube
    | linear_combination (g32p_determinant (g32p_literalRepresentative c) : ℂ) * hcube
  · change (g32p_inductionGenerator 0 false 2).character
        (g32p_literalRepresentative c) = _
    rw [g32p_determinantSupplier_generator_character]
    simp [g32p_determinantTracePair, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hd, ht, hone, g32p_determinant_inverse_square] <;> ring_nf <;> first
    | exact hcube
    | linear_combination (g32p_determinant (g32p_literalRepresentative c) : ℂ) * hcube
  · change (g32p_inductionGenerator 0 false 3).character
        (g32p_literalRepresentative c) = _
    rw [g32p_determinantSupplier_generator_character]
    simp [g32p_determinantTracePair, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hd, ht, hone, g32p_determinant_inverse_square] <;> ring_nf <;> first
    | exact hcube
    | linear_combination (g32p_determinant (g32p_literalRepresentative c) : ℂ) * hcube
  · change (g32p_inductionGenerator 0 true 2).character
        (g32p_literalRepresentative c) = _
    rw [g32p_determinantSupplier_generator_character]
    simp [g32p_determinantTracePair, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hd, ht, hone, g32p_determinant_inverse_square] <;> ring_nf <;> first
    | exact hcube
    | linear_combination (g32p_determinant (g32p_literalRepresentative c) : ℂ) * hcube
  · change (g32p_inductionGenerator 0 true 3).character
        (g32p_literalRepresentative c) = _
    rw [g32p_determinantSupplier_generator_character]
    simp [g32p_determinantTracePair, HurwitzPrymRex_ev_mul g32h_omega_sq_add,
      hd, ht, hone, g32p_determinant_inverse_square] <;> ring_nf <;> first
    | exact hcube
    | linear_combination (g32p_determinant (g32p_literalRepresentative c) : ℂ) * hcube

theorem g32p_determinantSupplier_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_determinantTraceRowIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega
        (g32p_literalTraceValue (g32p_determinantTraceRowIndex k) c) := by
  rw [g32p_determinantTrace_arithmetic]
  exact g32p_determinantTracePair_actual c k

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootEigen_absent_050_000 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_000 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_000 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_001 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_001 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_001 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_002 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_002 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_002 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_003 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_003 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_003 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_004 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_004 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_004 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_005 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_005 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_005 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_006 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_006 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_006 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_007 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_007 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_007 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_008 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_008 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_008 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_009 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_009 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_009 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_010 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_010 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_010 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_011 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_011 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_011 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_012 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_012 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_012 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_013 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_013 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_013 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_014 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_014 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_014 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_015 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_015 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_015 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_016 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_016 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_016 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_017 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_017 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_017 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_018 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_018 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_018 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_019 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_019 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_019 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_000 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_000 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_000 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_001 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_001 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_001 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_002 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_002 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_002 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_003 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_003 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_003 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_004 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_004 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_004 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_005 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_005 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_005 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_006 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_006 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_006 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_007 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_007 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_007 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_008 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_008 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_008 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_009 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_009 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_009 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_010 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_010 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_010 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_011 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_011 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_011 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_012 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_012 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_012 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_013 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_013 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_013 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_014 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_014 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_014 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_015 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_015 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_015 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_016 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_016 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_016 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_017 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_017 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_017 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_018 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_018 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_018 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_019 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_019 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_019 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_000 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_000 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_000 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_001 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_001 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_001 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_002 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_002 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_002 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_003 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_003 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_003 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_004 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_004 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_004 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_005 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_005 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_005 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_006 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_006 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_006 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_007 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_007 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_007 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_008 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_008 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_008 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_009 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_009 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_009 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_010 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_010 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_010 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_011 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_011 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_011 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_012 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_012 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_012 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_013 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_013 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_013 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_014 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_014 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_014 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_015 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_015 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_015 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_016 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_016 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_016 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_017 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_017 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_017 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_018 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_018 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_018 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_019 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_019 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_019 r s)) := by
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

theorem g32p_rootEigen_absent_050_020 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_020 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_020 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_021 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_021 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_021 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_022 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_022 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_022 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_023 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_023 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_023 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_024 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_024 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_024 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_025 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_025 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_025 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_026 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_026 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_026 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_027 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_027 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_027 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_028 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_028 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_028 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_029 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_029 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_029 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_030 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_030 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_030 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_031 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_031 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_031 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_032 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_032 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_032 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_033 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_033 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_033 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_034 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_034 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_034 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_035 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_035 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_035 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_036 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_036 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_036 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_037 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_037 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_037 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_038 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_038 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_038 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_039 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_039 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_039 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_020 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_020 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_020 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_021 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_021 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_021 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_022 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_022 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_022 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_023 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_023 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_023 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_024 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_024 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_024 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_025 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_025 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_025 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_026 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_026 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_026 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_027 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_027 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_027 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_028 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_028 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_028 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_029 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_029 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_029 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_030 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_030 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_030 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_031 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_031 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_031 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_032 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_032 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_032 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_033 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_033 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_033 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_034 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_034 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_034 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_035 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_035 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_035 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_036 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_036 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_036 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_037 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_037 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_037 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_038 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_038 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_038 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_039 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_039 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_039 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_020 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_020 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_020 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_021 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_021 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_021 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_022 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_022 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_022 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_023 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_023 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_023 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_024 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_024 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_024 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_025 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_025 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_025 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_026 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_026 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_026 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_027 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_027 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_027 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_028 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_028 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_028 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_029 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_029 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_029 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_030 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_030 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_030 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_031 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_031 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_031 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_032 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_032 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_032 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_033 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_033 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_033 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_034 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_034 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_034 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_035 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_035 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_035 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_036 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_036 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_036 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_037 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_037 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_037 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_038 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_038 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_038 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_039 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_039 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_039 r s)) := by
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

theorem g32p_rootEigen_absent_050_040 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_040 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_040 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_041 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_041 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_041 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_042 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_042 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_042 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_043 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_043 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_043 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_044 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_044 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_044 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_045 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_045 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_045 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_046 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_046 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_046 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_047 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_047 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_047 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_048 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_048 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_048 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_049 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_049 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_049 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_050 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_050 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_050 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_051 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_051 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_051 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_052 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_052 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_052 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_053 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_053 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_053 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_054 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_054 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_054 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_055 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_055 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_055 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_056 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_056 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_056 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_057 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_057 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_057 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_058 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_058 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_058 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_059 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_059 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_059 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_040 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_040 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_040 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_041 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_041 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_041 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_042 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_042 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_042 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_043 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_043 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_043 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_044 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_044 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_044 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_045 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_045 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_045 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_046 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_046 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_046 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_047 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_047 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_047 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_048 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_048 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_048 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_049 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_049 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_049 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_050 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_050 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_050 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_051 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_051 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_051 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_052 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_052 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_052 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_053 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_053 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_053 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_054 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_054 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_054 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_055 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_055 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_055 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_056 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_056 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_056 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_057 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_057 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_057 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_058 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_058 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_058 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_059 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_059 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_059 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_040 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_040 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_040 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_041 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_041 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_041 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_042 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_042 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_042 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_043 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_043 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_043 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_044 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_044 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_044 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_045 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_045 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_045 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_046 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_046 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_046 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_047 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_047 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_047 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_048 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_048 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_048 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_049 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_049 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_049 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_050 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_050 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_050 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_051 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_051 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_051 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_052 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_052 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_052 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_053 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_053 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_053 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_054 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_054 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_054 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_055 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_055 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_055 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_056 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_056 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_056 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_057 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_057 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_057 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_058 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_058 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_058 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_059 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_059 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_059 r s)) := by
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

theorem g32p_rootEigen_absent_050_060 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_060 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_060 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_061 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_061 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_061 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_062 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_062 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_062 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_063 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_063 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_063 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_064 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_064 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_064 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_065 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_065 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_065 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_066 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_066 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_066 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_067 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_067 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_067 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_068 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_068 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_068 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_069 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_069 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_069 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_070 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_070 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_070 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_071 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_071 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_071 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_072 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_072 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_072 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_073 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_073 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_073 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_074 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_074 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_074 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_075 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_075 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_075 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_076 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_076 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_076 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_077 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_077 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_077 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_078 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_078 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_078 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_079 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_079 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_079 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_060 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_060 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_060 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_061 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_061 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_061 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_062 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_062 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_062 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_063 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_063 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_063 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_064 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_064 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_064 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_065 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_065 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_065 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_066 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_066 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_066 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_067 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_067 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_067 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_068 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_068 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_068 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_069 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_069 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_069 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_070 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_070 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_070 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_071 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_071 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_071 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_072 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_072 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_072 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_073 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_073 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_073 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_074 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_074 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_074 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_075 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_075 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_075 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_076 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_076 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_076 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_077 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_077 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_077 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_078 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_078 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_078 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_079 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_079 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_079 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_060 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_060 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_060 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_061 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_061 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_061 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_062 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_062 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_062 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_063 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_063 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_063 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_064 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_064 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_064 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_065 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_065 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_065 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_066 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_066 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_066 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_067 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_067 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_067 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_068 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_068 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_068 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_069 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_069 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_069 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_070 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_070 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_070 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_071 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_071 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_071 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_072 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_072 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_072 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_073 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_073 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_073 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_074 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_074 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_074 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_075 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_075 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_075 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_076 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_076 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_076 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_077 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_077 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_077 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_078 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_078 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_078 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_079 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_079 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_079 r s)) := by
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

theorem g32p_rootEigen_absent_050_080 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_080 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_080 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_081 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_081 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_081 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_082 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_082 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_082 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_083 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_083 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_083 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_084 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_084 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_084 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_085 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_085 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_085 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_086 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_086 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_086 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_087 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_087 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_087 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_088 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_088 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_088 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_089 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_089 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_089 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_090 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_090 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_090 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_091 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_091 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_091 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_092 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_092 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_092 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_093 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_093 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_093 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_094 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_094 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_094 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_095 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_095 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_095 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_096 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_096 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_096 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_097 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_097 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_097 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_098 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_098 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_098 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_099 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_099 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_099 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_080 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_080 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_080 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_081 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_081 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_081 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_082 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_082 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_082 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_083 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_083 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_083 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_084 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_084 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_084 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_085 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_085 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_085 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_086 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_086 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_086 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_087 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_087 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_087 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_088 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_088 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_088 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_089 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_089 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_089 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_090 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_090 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_090 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_091 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_091 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_091 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_092 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_092 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_092 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_093 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_093 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_093 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_094 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_094 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_094 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_095 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_095 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_095 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_096 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_096 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_096 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_097 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_097 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_097 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_098 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_098 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_098 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_099 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_099 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_099 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_080 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_080 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_080 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_081 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_081 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_081 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_082 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_082 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_082 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_083 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_083 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_083 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_084 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_084 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_084 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_085 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_085 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_085 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_086 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_086 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_086 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_087 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_087 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_087 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_088 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_088 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_088 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_089 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_089 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_089 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_090 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_090 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_090 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_091 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_091 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_091 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_092 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_092 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_092 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_093 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_093 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_093 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_094 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_094 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_094 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_095 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_095 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_095 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_096 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_096 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_096 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_097 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_097 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_097 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_098 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_098 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_098 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_099 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_099 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_099 r s)) := by
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

theorem g32p_rootEigen_absent_050_100 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_100 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_100 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_101 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_101 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_101 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_102 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_102 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_102 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_103 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_103 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_103 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_104 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_104 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_104 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_105 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_105 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_105 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_106 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_106 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_106 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_107 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_107 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_107 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_108 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_108 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_108 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_109 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_109 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_109 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_110 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_110 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_110 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_111 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_111 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_111 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_112 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_112 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_112 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_113 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_113 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_113 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_114 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_114 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_114 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_115 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_115 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_115 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_116 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_116 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_116 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_117 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_117 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_117 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_118 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_118 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_118 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_119 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_119 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_119 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_100 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_100 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_100 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_101 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_101 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_101 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_102 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_102 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_102 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_103 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_103 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_103 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_104 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_104 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_104 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_105 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_105 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_105 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_106 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_106 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_106 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_107 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_107 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_107 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_108 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_108 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_108 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_109 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_109 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_109 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_110 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_110 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_110 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_111 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_111 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_111 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_112 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_112 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_112 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_113 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_113 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_113 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_114 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_114 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_114 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_115 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_115 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_115 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_116 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_116 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_116 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_117 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_117 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_117 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_118 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_118 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_118 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_119 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_119 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_119 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_100 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_100 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_100 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_101 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_101 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_101 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_102 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_102 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_102 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_103 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_103 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_103 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_104 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_104 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_104 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_105 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_105 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_105 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_106 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_106 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_106 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_107 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_107 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_107 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_108 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_108 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_108 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_109 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_109 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_109 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_110 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_110 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_110 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_111 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_111 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_111 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_112 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_112 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_112 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_113 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_113 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_113 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_114 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_114 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_114 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_115 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_115 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_115 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_116 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_116 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_116 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_117 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_117 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_117 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_118 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_118 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_118 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_119 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_119 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_119 r s)) := by
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

theorem g32p_rootEigen_absent_050_120 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_120 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_120 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_121 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_121 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_121 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_122 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_122 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_122 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_123 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_123 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_123 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_124 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_124 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_124 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_125 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_125 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_125 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_126 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_126 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_126 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_127 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_127 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_127 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_128 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_128 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_128 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_129 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_129 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_129 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_130 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_130 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_130 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_131 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_131 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_131 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_132 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_132 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_132 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_133 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_133 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_133 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_134 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_134 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_134 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_135 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_135 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_135 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_136 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_136 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_136 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_137 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_137 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_137 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_138 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_138 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_138 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_050_139 :
    HurwitzPrymRex_mmul g32p_literalMatrix_050 g32p_rootMatrix_139 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_139 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_120 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_120 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_120 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_121 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_121 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_121 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_122 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_122 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_122 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_123 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_123 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_123 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_124 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_124 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_124 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_125 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_125 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_125 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_126 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_126 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_126 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_127 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_127 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_127 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_128 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_128 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_128 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_129 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_129 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_129 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_130 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_130 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_130 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_131 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_131 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_131 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_132 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_132 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_132 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_133 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_133 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_133 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_134 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_134 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_134 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_135 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_135 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_135 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_136 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_136 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_136 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_137 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_137 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_137 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_138 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_138 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_138 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_059_139 :
    HurwitzPrymRex_mmul g32p_literalMatrix_059 g32p_rootMatrix_139 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨1, 0⟩ (g32p_rootMatrix_139 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_120 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_120 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_120 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_121 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_121 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_121 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_122 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_122 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_122 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_123 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_123 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_123 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_124 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_124 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_124 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_125 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_125 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_125 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_126 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_126 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_126 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_127 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_127 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_127 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_128 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_128 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_128 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_129 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_129 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_129 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_130 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_130 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_130 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_131 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_131 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_131 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_132 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_132 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_132 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_133 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_133 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_133 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_134 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_134 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_134 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_135 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_135 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_135 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_136 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_136 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_136 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_137 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_137 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_137 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_138 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_138 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_138 r s)) := by
  decide +kernel

theorem g32p_rootEigen_absent_074_139 :
    HurwitzPrymRex_mmul g32p_literalMatrix_074 g32p_rootMatrix_139 ≠
      (fun r s => HurwitzPrymRex_Zw.mul ⟨0, 1⟩ (g32p_rootMatrix_139 r s)) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
