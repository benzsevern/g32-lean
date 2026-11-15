import HodgeLean.Foundations.Program.G32Native.AbelCollisionDescendedTrace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Indexed collision blocks in the actual coefficient vector -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Type} [Fintype A] [DecidableEq A] (m : A → ℕ)

/-- Insert a coefficient or root vector in one specified collision block. -/
def collisionBlockInsert (a : A) (u : Fin (m a) → ℂ) : (Σ b, Fin (m b)) → ℂ :=
  fun s => if h : s.1 = a then u (Fin.cast (congrArg m h) s.2) else 0

/-- Insertion retains every indexed entry of the specified block. -/
@[simp] theorem collisionBlockInsert_self (a : A) (u : Fin (m a) → ℂ) (j : Fin (m a)) :
    collisionBlockInsert m a u ⟨a, j⟩ = u j := by
  simp [collisionBlockInsert]

/-- Every other block remains zero. -/
@[simp] theorem collisionBlockInsert_other {a b : A} (hab : b ≠ a)
    (u : Fin (m a) → ℂ) (j : Fin (m b)) : collisionBlockInsert m a u ⟨b, j⟩ = 0 := by
  simp [collisionBlockInsert, hab]

/-- The block insertion is the actual linear inclusion of that coordinate block. -/
def collisionBlockInsertion (a : A) :
    (Fin (m a) → ℂ) →ₗ[ℂ] ((Σ b, Fin (m b)) → ℂ) where
  toFun := collisionBlockInsert m a
  map_add' u v := by
    funext ⟨b, j⟩
    by_cases hb : b = a
    · subst b
      simp only [Pi.add_apply, collisionBlockInsert_self]
    · simp only [Pi.add_apply, collisionBlockInsert_other m hb, add_zero]
  map_smul' c u := by
    funext ⟨b, j⟩
    by_cases hb : b = a
    · subst b
      simp only [Pi.smul_apply, collisionBlockInsert_self, RingHom.id_apply]
    · simp only [Pi.smul_apply, collisionBlockInsert_other m hb, smul_zero, RingHom.id_apply]

/-- Monic coefficients in the same indexed collision blocks. -/
def collisionBlockCoefficients (z : (Σ b, Fin (m b)) → ℂ) : (Σ b, Fin (m b)) → ℂ :=
  fun s => collisionMonicCoefficients (fun j => z ⟨s.1, j⟩) s.2

/-- The lower coefficients of a full collision polynomial vanish. -/
theorem collisionMonicCoefficients_zero (n : ℕ) :
    collisionMonicCoefficients (0 : Fin n → ℂ) = 0 := by
  ext j
  simp only [collisionMonicCoefficients, Pi.zero_apply, map_zero, sub_zero,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Polynomial.coeff_X_pow,
    if_neg (Nat.ne_of_lt j.isLt)]

/-- Block coefficients commute with insertion, including every zero block. -/
theorem collisionBlockCoefficients_insert (a : A) (u : Fin (m a) → ℂ) :
    collisionBlockCoefficients m (collisionBlockInsert m a u) =
      collisionBlockInsert m a (collisionMonicCoefficients u) := by
  ext ⟨b, j⟩
  by_cases hb : b = a
  · subst b
    simp only [collisionBlockCoefficients, collisionBlockInsert_self]
  · simp only [collisionBlockCoefficients, collisionBlockInsert_other m hb]
    change collisionMonicCoefficients (0 : Fin (m b) → ℂ) j = 0
    rw [collisionMonicCoefficients_zero]
    rfl

/-- A basis vector of one block is the original total-coordinate basis vector. -/
theorem collisionBlockInsert_single (a : A) (j : Fin (m a)) (c : ℂ) :
    collisionBlockInsert m a (Pi.single j c) = Pi.single ⟨a, j⟩ c := by
  ext ⟨b, k⟩
  by_cases hb : b = a
  · subst b
    simp [collisionBlockInsert, Pi.single_apply]
  · have he : (⟨b, k⟩ : Σ b, Fin (m b)) ≠ ⟨a, j⟩ := by
      intro h
      exact hb (congrArg Sigma.fst h)
    simp [collisionBlockInsert, hb, Pi.single_apply, he]

#print axioms collisionBlockInsertion
#print axioms collisionMonicCoefficients_zero
#print axioms collisionBlockCoefficients_insert
#print axioms collisionBlockInsert_single
end HodgeLean.Foundations.Program.G32Native
