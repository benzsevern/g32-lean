import HodgeLean.Foundations.Program.G32PropFourSixArchiveBridge

noncomputable section

open HodgeLean.Papers

namespace HodgeLean.Foundations.Program

def g32p_archiveCoordinates : Fin 4 ≃ Fin 4 where
  toFun i := ![1, 3, 2, 0] i
  invFun i := ![3, 0, 2, 1] i
  left_inv := by decide
  right_inv := by decide

def g32p_archiveGenerators : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![![![g32h_omega/3 + 2/3, 2*g32h_omega/3 + 1/3, -2*g32h_omega/3 - 1/3, 0],
    ![-g32h_omega/3 - 2/3, g32h_omega/3 + 2/3, 1/3 - g32h_omega/3, 0],
    ![g32h_omega/3 + 2/3, 1/3 - g32h_omega/3, g32h_omega/3 + 2/3, 0],
    ![0, 0, 0, 1]],
    ![![g32h_omega/3 + 2/3, 0, -g32h_omega/3 - 2/3, g32h_omega/3 - 1/3],
    ![0, 1, 0, 0],
    ![2*g32h_omega/3 + 1/3, 0, g32h_omega/3 + 2/3, 2*g32h_omega/3 + 1/3],
    ![g32h_omega/3 - 1/3, 0, -g32h_omega/3 - 2/3, g32h_omega/3 + 2/3]],
    ![![g32h_omega/3 + 2/3, -g32h_omega/3 - 2/3, g32h_omega/3 - 1/3, 0],
    ![2*g32h_omega/3 + 1/3, g32h_omega/3 + 2/3, 2*g32h_omega/3 + 1/3, 0],
    ![g32h_omega/3 - 1/3, -g32h_omega/3 - 2/3, g32h_omega/3 + 2/3, 0],
    ![0, 0, 0, 1]],
    ![![g32h_omega/3 + 2/3, 2*g32h_omega/3 + 1/3, g32h_omega/3 + 2/3, 0],
    ![-g32h_omega/3 - 2/3, g32h_omega/3 + 2/3, 2*g32h_omega/3 + 1/3, 0],
    ![-2*g32h_omega/3 - 1/3, -g32h_omega/3 - 2/3, g32h_omega/3 + 2/3, 0],
    ![0, 0, 0, 1]]]

def g32p_archiveWords : Fin 4 → List (Fin 4) :=
  ![[3, 0, 3, 3], [1, 1, 3, 0, 3, 3, 1], [1, 0, 0, 3, 2, 1, 3, 2, 0, 2], [3, 0, 2]]

def g32p_archiveIntegralGenerators : Fin 4 → HurwitzPrymRex_Mat :=
  ![![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
    ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩],
    ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
    ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩],
    ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
    ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩],
    ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩],
    ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩],
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]]

def g32p_integralWord : List (Fin 4) → HurwitzPrymRex_Mat
  | [] => HurwitzPrymRex_mone
  | i :: is => HurwitzPrymRex_mmul
      (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i.val) (g32p_integralWord is)

def g32p_word (w : List (Fin 4)) : g32p_G := (w.map b4b_generators).prod

theorem g32p_integralGenerator_map (i : Fin 4) :
    b4b_toMatrix (b4b_generators i) = HurwitzPrymRex_g32conj
      (HurwitzPrymRex_evM g32h_omega (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne i.val)) := by
  fin_cases i
  · exact HurwitzPrymRex_g32_conj0.symm
  · exact HurwitzPrymRex_g32_conj1.symm
  · exact HurwitzPrymRex_g32_conj2.symm
  · exact HurwitzPrymRex_g32_conj3.symm

theorem g32p_integralWord_map (w : List (Fin 4)) :
    b4b_toMatrix (g32p_word w) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_integralWord w)) := by
  induction w with
  | nil => simp only [g32p_word, List.map_nil, List.prod_nil, map_one,
      g32p_integralWord, HurwitzPrymRex_evM_mone]
  | cons i is ih =>
      change b4b_toMatrix (b4b_generators i * g32p_word is) = _
      rw [map_mul, g32p_integralWord, HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
        map_mul, ← ih, ← g32p_integralGenerator_map]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
theorem g32p_archiveWordIntegral_0 :
    g32p_integralWord (g32p_archiveWords 0) = g32p_archiveIntegralGenerators 0 := by
  decide +kernel

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
theorem g32p_archiveWordIntegral_1 :
    g32p_integralWord (g32p_archiveWords 1) = g32p_archiveIntegralGenerators 1 := by
  decide +kernel

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
theorem g32p_archiveWordIntegral_2 :
    g32p_integralWord (g32p_archiveWords 2) = g32p_archiveIntegralGenerators 2 := by
  decide +kernel

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
theorem g32p_archiveWordIntegral_3 :
    g32p_integralWord (g32p_archiveWords 3) = g32p_archiveIntegralGenerators 3 := by
  decide +kernel

theorem g32p_archiveWordIntegral (i : Fin 4) :
    g32p_integralWord (g32p_archiveWords i) = g32p_archiveIntegralGenerators i := by
  fin_cases i
  · exact g32p_archiveWordIntegral_0
  · exact g32p_archiveWordIntegral_1
  · exact g32p_archiveWordIntegral_2
  · exact g32p_archiveWordIntegral_3

set_option maxHeartbeats 400000 in
theorem g32p_archiveGenerator_transport_0 :
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
      (g32p_archiveIntegralGenerators 0)) =
        (g32p_archiveGenerators 0).submatrix g32p_archiveCoordinates g32p_archiveCoordinates := by
  ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [HurwitzPrymRex_g32conj, HurwitzPrymRex_g32P, HurwitzPrymRex_g32Pinv,
      HurwitzPrymRex_evM, HurwitzPrymRex_ev, g32p_archiveIntegralGenerators,
      g32p_archiveGenerators, Matrix.submatrix, g32p_archiveCoordinates,
      Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Fin.sum_univ_four] <;>
    first
    | (right; trivial)
    | (right; papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)
    | (papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)

set_option maxHeartbeats 400000 in
theorem g32p_archiveGenerator_transport_1 :
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
      (g32p_archiveIntegralGenerators 1)) =
        (g32p_archiveGenerators 1).submatrix g32p_archiveCoordinates g32p_archiveCoordinates := by
  ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [HurwitzPrymRex_g32conj, HurwitzPrymRex_g32P, HurwitzPrymRex_g32Pinv,
      HurwitzPrymRex_evM, HurwitzPrymRex_ev, g32p_archiveIntegralGenerators,
      g32p_archiveGenerators, Matrix.submatrix, g32p_archiveCoordinates,
      Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Fin.sum_univ_four] <;>
    first
    | (right; trivial)
    | (right; papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)
    | (papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)

set_option maxHeartbeats 400000 in
theorem g32p_archiveGenerator_transport_2 :
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
      (g32p_archiveIntegralGenerators 2)) =
        (g32p_archiveGenerators 2).submatrix g32p_archiveCoordinates g32p_archiveCoordinates := by
  ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [HurwitzPrymRex_g32conj, HurwitzPrymRex_g32P, HurwitzPrymRex_g32Pinv,
      HurwitzPrymRex_evM, HurwitzPrymRex_ev, g32p_archiveIntegralGenerators,
      g32p_archiveGenerators, Matrix.submatrix, g32p_archiveCoordinates,
      Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Fin.sum_univ_four] <;>
    first
    | (right; trivial)
    | (right; papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)
    | (papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)

set_option maxHeartbeats 400000 in
theorem g32p_archiveGenerator_transport_3 :
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
      (g32p_archiveIntegralGenerators 3)) =
        (g32p_archiveGenerators 3).submatrix g32p_archiveCoordinates g32p_archiveCoordinates := by
  ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [HurwitzPrymRex_g32conj, HurwitzPrymRex_g32P, HurwitzPrymRex_g32Pinv,
      HurwitzPrymRex_evM, HurwitzPrymRex_ev, g32p_archiveIntegralGenerators,
      g32p_archiveGenerators, Matrix.submatrix, g32p_archiveCoordinates,
      Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Fin.sum_univ_four] <;>
    first
    | (right; trivial)
    | (right; papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)
    | (papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add)

theorem g32p_archiveGenerator_transport (i : Fin 4) :
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
      (g32p_archiveIntegralGenerators i)) =
        (g32p_archiveGenerators i).submatrix g32p_archiveCoordinates g32p_archiveCoordinates := by
  fin_cases i
  · exact g32p_archiveGenerator_transport_0
  · exact g32p_archiveGenerator_transport_1
  · exact g32p_archiveGenerator_transport_2
  · exact g32p_archiveGenerator_transport_3

theorem g32p_archiveGenerator_word (i : Fin 4) :
    b4b_toMatrix (g32p_word (g32p_archiveWords i)) =
      (g32p_archiveGenerators i).submatrix g32p_archiveCoordinates g32p_archiveCoordinates := by
  rw [g32p_integralWord_map, g32p_archiveWordIntegral, g32p_archiveGenerator_transport]

end HodgeLean.Foundations.Program
