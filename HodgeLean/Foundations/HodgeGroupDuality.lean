import HodgeLean.Foundations.HodgeGroupAlgebraicDefs

/-! Dual matrix representations and rational algebraic hulls. -/

noncomputable section
namespace HodgeLean.Foundations

open MvPolynomial
variable {n : ℕ}

/-- Transposition on invertible matrices, with reversed multiplication. -/
def g2_dualTranspose (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    Matrix.GeneralLinearGroup (Fin n) ℂ where
  val := (g : Matrix (Fin n) (Fin n) ℂ).transpose
  inv := (↑(g⁻¹) : Matrix (Fin n) (Fin n) ℂ).transpose
  val_inv := by rw [← Matrix.transpose_mul]; simp
  inv_val := by rw [← Matrix.transpose_mul]; simp

@[simp] theorem g2_dualTranspose_twice (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g2_dualTranspose (g2_dualTranspose g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose _

@[simp] theorem g2_dualTranspose_one :
    g2_dualTranspose (1 : Matrix.GeneralLinearGroup (Fin n) ℂ) = 1 := by
  apply Units.ext
  exact Matrix.transpose_one

@[simp] theorem g2_dualTranspose_mul (g h : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g2_dualTranspose (g * h) = g2_dualTranspose h * g2_dualTranspose g := by
  apply Units.ext
  exact Matrix.transpose_mul _ _

@[simp] theorem g2_dualTranspose_inv (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g2_dualTranspose (g⁻¹) = (g2_dualTranspose g)⁻¹ := by
  apply Units.ext
  rfl

/-- The action on the dual space is inverse transpose. -/
def g2_contragredient : Matrix.GeneralLinearGroup (Fin n) ℂ ≃*
    Matrix.GeneralLinearGroup (Fin n) ℂ where
  toFun g := g2_dualTranspose (g⁻¹)
  invFun g := g2_dualTranspose (g⁻¹)
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := by simp

/-- Pulling back a rational algebraic subgroup under transpose preserves rational algebraicity. -/
theorem g2_isRatAlgSubgroup_transpose {G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)}
    (hG : g2_IsRatAlgSubgroup G) : g2_IsRatAlgSubgroup (g2_dualTranspose ⁻¹' G) := by
  obtain ⟨⟨S, hS⟩, h1, hmul, hinv⟩ := hG
  refine ⟨⟨MvPolynomial.rename Prod.swap '' S, ?_⟩, ?_, ?_, ?_⟩
  · ext g
    rw [Set.mem_preimage, hS]
    have hc : g1_coords (g2_dualTranspose g) = g1_coords g ∘ Prod.swap := rfl
    constructor
    · intro hg f hf
      obtain ⟨p, hp, rfl⟩ := hf
      simpa only [MvPolynomial.aeval_rename, ← hc] using hg p hp
    · intro hg p hp
      have := hg (MvPolynomial.rename Prod.swap p) ⟨p, hp, rfl⟩
      simpa only [MvPolynomial.aeval_rename, ← hc] using this
  · simpa only [Set.mem_preimage, g2_dualTranspose_one] using h1
  · intro x hx y hy
    change g2_dualTranspose (x * y) ∈ G
    rw [g2_dualTranspose_mul]
    exact hmul _ hy _ hx
  · intro x hx
    change g2_dualTranspose (x⁻¹) ∈ G
    rw [g2_dualTranspose_inv]
    exact hinv _ hx

end HodgeLean.Foundations
