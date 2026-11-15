import HodgeLean.Foundations.Program.RigidStartingSystemDefs

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

def b65r_centralizerAlgEquiv {n m : ℕ}
    (e : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    b65r_centralizer A ≃ₗ[ℂ] b65r_centralizer (e A) where
  toFun X := ⟨e X.val, by
    change e A * e X.val = e X.val * e A
    rw [← map_mul, ← map_mul, X.property]⟩
  invFun Y := ⟨e.symm Y.val, by
    apply e.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply]
    exact Y.property⟩
  left_inv X := by ext i j; exact congrFun (congrFun (e.symm_apply_apply X.val) i) j
  right_inv Y := by ext i j; exact congrFun (congrFun (e.apply_symm_apply Y.val) i) j
  map_add' X Y := by apply Subtype.ext; exact map_add e X.val Y.val
  map_smul' c X := by apply Subtype.ext; exact map_smul e c X.val

def b65r_diagonalCentralizerEquiv {n : ℕ} (d : Fin n → ℂ) :
    b65r_centralizer (diagonal d) ≃ₗ[ℂ]
      ({p : Fin n × Fin n // d p.1 = d p.2} → ℂ) := by
  classical
  exact {
    toFun X p := X.val p.val.1 p.val.2
    invFun f := ⟨fun i j ↦ if h : d i = d j then f ⟨(i,j), h⟩ else 0, by
      let M : Matrix (Fin n) (Fin n) ℂ :=
        fun i j ↦ if h : d i = d j then f ⟨(i,j), h⟩ else 0
      change diagonal d * M = M * diagonal d
      apply Matrix.ext
      intro i j
      rw [diagonal_mul, mul_diagonal]
      dsimp only [M]
      split_ifs with h
      · rw [h, mul_comm]
      · simp only [mul_zero, zero_mul]⟩
    left_inv X := by
      apply Subtype.ext
      ext i j
      dsimp only
      split_ifs with h
      · rfl
      · have hc := congrFun (congrFun X.property i) j
        simp only [diagonal_mul, mul_diagonal] at hc
        have he : (d i-d j)*X.val i j = 0 := by linear_combination hc
        exact ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr h)).symm
    right_inv f := by
      funext p
      dsimp only
      rw [dite_eq_left p.property]
    map_add' X Y := rfl
    map_smul' c X := rfl }

theorem b65r_diagonal_centralizer_finrank {n : ℕ} (d : Fin n → ℂ) :
    Module.finrank ℂ (b65r_centralizer (diagonal d)) =
      Nat.card {p : Fin n × Fin n // d p.1 = d p.2} := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [(b65r_diagonalCentralizerEquiv d).finrank_eq]
  simp only [Module.finrank_fintype_fun_eq_card]

def b65r_matrixConj {n : ℕ} (Q : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := Q*X*↑(Q⁻¹)
  invFun X := ↑(Q⁻¹)*X*Q
  left_inv X := by simp [mul_assoc]
  right_inv X := by simp [mul_assoc]
  map_mul' X Y := by simp [mul_assoc]
  map_add' X Y := by simp only [mul_add, add_mul]
  commutes' c := by
    simp [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_assoc]

theorem b65r_centralizer_finrank_eigenbasis {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (d : Fin n → ℂ) (hG : G*Q = Q*diagonal d) :
    Module.finrank ℂ (b65r_centralizer G) =
      Nat.card {p : Fin n × Fin n // d p.1 = d p.2} := by
  have he : b65r_matrixConj Q (diagonal d) = G := by
    change Q.val*diagonal d*(Q⁻¹).val = G
    rw [← hG]
    simp [mul_assoc]
  have hd := (b65r_centralizerAlgEquiv (b65r_matrixConj Q) (diagonal d)).finrank_eq
  rw [he] at hd
  rw [← hd, b65r_diagonal_centralizer_finrank]

end HodgeLean.Foundations.Program
