import HodgeLean.Foundations.Program.BraidCertificateDefs
import Mathlib.Algebra.QuadraticAlgebra.Basic

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers

abbrev b65b_Q := QuadraticAlgebra ℚ (-1) (-1)

instance b65b_noRoot : Fact (∀ r : ℚ, r ^ 2 ≠ -1 + -1 * r) := by
  constructor
  intro r h
  nlinarith [sq_nonneg (r + 1/2)]

def b65b_qOmega : b65b_Q := QuadraticAlgebra.omega

def b65b_qMatrices : Fin 4 → Matrix (Fin 4) (Fin 4) b65b_Q :=
  ![g32R1 b65b_qOmega, g32R2 b65b_qOmega, g32X b65b_qOmega, g32Y b65b_qOmega]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_qOrders : ∀ i, b65b_qMatrices i ^ (![3, 3, 4, 3] : Fin 4 → ℕ) i = 1 := by
  decide +kernel

def b65b_qGenerators (i : Fin 4) : (Matrix (Fin 4) (Fin 4) b65b_Q)ˣ where
  val := b65b_qMatrices i
  inv := b65b_qMatrices i ^ ((![2, 2, 3, 2] : Fin 4 → ℕ) i)
  val_inv := by
    have h := b65b_qOrders i
    fin_cases i <;> simpa [pow_succ, mul_assoc] using h
  inv_val := by
    have h := b65b_qOrders i
    fin_cases i <;> simpa [pow_succ] using h

noncomputable def b65b_embedding : b65b_Q →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨g32h_omega, by
    norm_num [Algebra.smul_def]
    linear_combination g32h_omega_sq_add⟩

noncomputable def b65b_realize : (Matrix (Fin 4) (Fin 4) b65b_Q)ˣ →*
    (Matrix (Fin 4) (Fin 4) ℂ)ˣ :=
  Units.map b65b_embedding.mapMatrix.toMonoidHom

theorem b65b_embedding_omega : b65b_embedding b65b_qOmega = g32h_omega := by
  simp [b65b_embedding, b65b_qOmega, QuadraticAlgebra.lift]

theorem b65b_realize_generators (i : Fin 4) :
    b65b_realize (b65b_qGenerators i) = b4b_toMatrix.toHomUnits (b4b_generators i) := by
  apply Units.ext
  change (b65b_qMatrices i).map b65b_embedding = b4b_toMatrix (b4b_generators i)
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [b65b_qMatrices, b4b_generators, b4b_toMatrix,
      g32R1, g32R2, g32X, g32Y, b65b_embedding_omega] <;>
    norm_num [b65b_embedding, QuadraticAlgebra.lift,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

def b65b_qCut : Fin 3 → (Matrix (Fin 4) (Fin 4) b65b_Q)ˣ :=
  ![b65b_qGenerators 0, b65b_qGenerators 1,
    b65b_qGenerators 1 * b65b_qGenerators 2 * (b65b_qGenerators 1)⁻¹]

def b65b_qEval (w : List (Fin 3 × ℤ)) : (Matrix (Fin 4) (Fin 4) b65b_Q)ˣ :=
  (w.reverse.map (fun a ↦ b65b_qCut a.1 ^ a.2)).prod

def b65b_qDecode (A : Matrix (Fin 4) (Fin 4) (ℤ × ℤ)) :
    Matrix (Fin 4) (Fin 4) b65b_Q :=
  fun i j ↦ ((A i j).1 + (A i j).2 * b65b_qOmega) / 3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_qLiteralInitial : ∀ i,
    (b65b_qEval (b65b_initialWords i)).val = b65b_qDecode (b65b_initialIntegral i) := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 400000 in
theorem b65b_qLiteralFinal : ∀ i,
    (b65b_qEval (b65b_finalWords i)).val = b65b_qDecode (b65b_finalIntegral i) := by
  intro i
  fin_cases i <;> decide +kernel

theorem b65b_realize_cut (i : Fin 3) :
    b65b_realize (b65b_qCut i) = b4b_toMatrix.toHomUnits (b65b_cut i) := by
  fin_cases i <;>
    simp [b65b_qCut, b65b_cut, b65b_realize_generators, map_mul, map_inv]

theorem b65b_realize_eval (w : List (Fin 3 × ℤ)) :
    b65b_realize (b65b_qEval w) = b4b_toMatrix.toHomUnits (b65b_eval w) := by
  simp only [b65b_qEval, b65b_eval, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp_apply, map_zpow, b65b_realize_cut]

theorem b65b_realize_decode (A : Matrix (Fin 4) (Fin 4) (ℤ × ℤ)) :
    (b65b_qDecode A).map b65b_embedding = b65b_decode A := by
  ext i j
  simp [b65b_qDecode, b65b_decode, b65b_embedding_omega]
  norm_num [b65b_embedding, QuadraticAlgebra.lift,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

end HodgeLean.Foundations.Program
