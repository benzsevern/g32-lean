import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Lean.Elab.Tactic.Omega

/-! # The common-zero argument in the projective modification step -/
noncomputable section
namespace HodgeLean.Foundations.Program.G32Native

/-- Fewer than k linear forms on k homogeneous coordinates have a common
nonzero vector. This is the homogeneous version on a hyperplane P^(k−1).
Source: Hartshorne, Algebraic Geometry, I.2, linear projective subspaces. -/
theorem paired_c3_linear_common_zero
    {K : Type*} [Field K] {k a : ℕ} (ha : a < k)
    (l : (Fin k → K) →ₗ[K] (Fin a → K)) :
    ∃ v : Fin k → K, v ≠ 0 ∧ l v = 0 := by
  by_contra h
  have hi : Function.Injective l := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hv'
    exact h ⟨v, hv', hv⟩
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  simp only [Module.finrank_fin_fun] at hd
  omega

/-- If the combined linear and constant relation coefficients never all
vanish on the hyperplane, a constant coefficient is nonzero. -/
theorem paired_c3_modification_constant_ne_zero
    {K : Type*} [Field K] {k a b : ℕ} (ha : a < k)
    (l : (Fin k → K) →ₗ[K] (Fin a → K)) (mu : Fin b → K)
    (h : ∀ v : Fin k → K, v ≠ 0 → l v ≠ 0 ∨ mu ≠ 0) :
    mu ≠ 0 := by
  obtain ⟨v, hv, hl⟩ := paired_c3_linear_common_zero ha l
  exact (h v hv).resolve_left (not_not.mpr hl)

#print axioms paired_c3_linear_common_zero
#print axioms paired_c3_modification_constant_ne_zero
end HodgeLean.Foundations.Program.G32Native
