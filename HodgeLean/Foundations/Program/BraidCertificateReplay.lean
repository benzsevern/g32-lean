import HodgeLean.Foundations.Program.BraidCertificateReplayJoin

namespace HodgeLean.Foundations.Program

theorem b65b_realize_reflection (w : List (Fin 4)) :
    b65b_realize (b65b_qReflection w) = b4b_toMatrix.toHomUnits (b4b_reflection w) := by
  simp [b65b_qReflection, b4b_reflection, map_mul, map_inv,
    map_list_prod, List.map_map, Function.comp_def, b65b_realize_generators]

theorem b65b_realize_columnRoot (i : Fin 13) :
    b65b_realize (b65b_qColumnRoot i) = b4b_toMatrix.toHomUnits (b65s_columnRoot i) := by
  fin_cases i <;>
    simp [b65b_qColumnRoot, b65s_columnRoot, b65b_qRoot, b4b_root,
      map_mul, map_inv, map_pow, b65b_realize_generators, b65b_realize_reflection]

def b65b_arithmeticMove : b65s_Move → Bool
  | .positive _ => true
  | .negative _ => true
  | .conjugate _ => false

theorem b65b_qWord_realize (w : List b65s_Move)
    (hw : w.all b65b_arithmeticMove = true)
    (t : Fin 13 → (Matrix (Fin 4) (Fin 4) b65b_Q)ˣ) (s : Fin 13 → b4b_Group)
    (ht : ∀ i, b65b_realize (t i) = b4b_toMatrix.toHomUnits (s i)) :
    ∀ i, b65b_realize (b65b_qWord w t i) =
      b4b_toMatrix.toHomUnits (b65s_word w s i) := by
  induction w generalizing t s with
  | nil => exact ht
  | cons m w ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    apply ih hw.2 (b65b_qStep m t) (b65s_step m s)
    intro i
    cases m with
    | positive k =>
      simp only [b65b_qStep, b65s_step, b4_braid, Function.update_apply]
      split_ifs <;> simp [map_mul, map_inv, ht]
    | negative k =>
      simp only [b65b_qStep, b65s_step, Function.update_apply]
      split_ifs <;> simp [map_mul, map_inv, ht]
    | conjugate g => simp [b65b_arithmeticMove] at hw

end HodgeLean.Foundations.Program
