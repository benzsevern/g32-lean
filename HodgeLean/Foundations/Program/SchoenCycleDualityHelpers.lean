import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Field.Rat

/-! # Adjoint maps for rational middle pairings
Perfect pairings determine the transfer uniquely once the geometric pullback
and traces have been constructed.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

variable {V W : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

/-- The adjoint of pullback for a perfect target pairing. -/
def s2e_pairingAdjoint (B₀ : V →ₗ[ℚ] Module.Dual ℚ V)
    (hB₀ : Function.Bijective B₀) (Br : W →ₗ[ℚ] Module.Dual ℚ W)
    (f : V →ₗ[ℚ] W) : W →ₗ[ℚ] V :=
  (LinearEquiv.ofBijective B₀ hB₀).symm.toLinearMap ∘ₗ
    ((LinearMap.dualMap f) ∘ₗ Br)

/-- Evaluation of the adjoint gives the required pairing equation. -/
theorem s2e_pairingAdjoint_pair (B₀ : V →ₗ[ℚ] Module.Dual ℚ V)
    (hB₀ : Function.Bijective B₀) (Br : W →ₗ[ℚ] Module.Dual ℚ W)
    (f : V →ₗ[ℚ] W) (u : W) (v : V) :
    B₀ (s2e_pairingAdjoint B₀ hB₀ Br f u) v = Br u (f v) := by
  have h := (LinearEquiv.ofBijective B₀ hB₀).apply_symm_apply
    ((LinearMap.dualMap f) (Br u))
  exact congrArg (fun l : Module.Dual ℚ V => l v) h

/-- The pairing equation uniquely specifies the transfer. -/
theorem s2e_pairingAdjoint_unique (B₀ : V →ₗ[ℚ] Module.Dual ℚ V)
    (hB₀ : Function.Bijective B₀) (Br : W →ₗ[ℚ] Module.Dual ℚ W)
    (f : V →ₗ[ℚ] W) (G : W →ₗ[ℚ] V)
    (hG : ∀ u v, B₀ (G u) v = Br u (f v)) :
    G = s2e_pairingAdjoint B₀ hB₀ Br f := by
  ext u
  apply hB₀.1
  ext v
  rw [hG, s2e_pairingAdjoint_pair]

/-- Preservation of the pairing makes the adjoint a retraction. -/
theorem s2e_pairingAdjoint_retraction (B₀ : V →ₗ[ℚ] Module.Dual ℚ V)
    (hB₀ : Function.Bijective B₀) (Br : W →ₗ[ℚ] Module.Dual ℚ W)
    (f : V →ₗ[ℚ] W) (hf : ∀ u v, Br (f u) (f v) = B₀ u v) (u : V) :
    s2e_pairingAdjoint B₀ hB₀ Br f (f u) = u := by
  apply hB₀.1
  ext v
  rw [s2e_pairingAdjoint_pair, hf]

/-- Adjoints intertwine actions whose pairing transposes commute with pullback. -/
theorem s2e_pairingAdjoint_intertwines
    (B₀ : V →ₗ[ℚ] Module.Dual ℚ V) (hB₀ : Function.Bijective B₀)
    (Br : W →ₗ[ℚ] Module.Dual ℚ W) (f : V →ₗ[ℚ] W)
    (D₀ E₀ : V →ₗ[ℚ] V) (Dr Er : W →ₗ[ℚ] W)
    (h₀ : ∀ u v, B₀ (D₀ u) v = B₀ u (E₀ v))
    (hr : ∀ u v, Br (Dr u) v = Br u (Er v))
    (hf : ∀ v, Er (f v) = f (E₀ v)) (u : W) :
    s2e_pairingAdjoint B₀ hB₀ Br f (Dr u) =
      D₀ (s2e_pairingAdjoint B₀ hB₀ Br f u) := by
  apply hB₀.1
  ext v
  rw [s2e_pairingAdjoint_pair, hr, hf, h₀, s2e_pairingAdjoint_pair]

end HodgeLean.Foundations.Program
