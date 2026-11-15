import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Rat.Cast.Order

/-! # Nonzero vectors in a single component coordinate space -/

noncomputable section
namespace HodgeLean.Foundations.QuotientDuality

/-- An injective single-component coordinate map is surjective once its source has a nonzero vector. -/
lemma retained_singleton_coordinates_surjective
    {V I : Type*} [AddCommGroup V] [Module ℚ V] [Subsingleton I] [Nonempty I]
    (F : V →ₗ[ℚ] (I → ℚ)) (hF : Function.Injective F)
    (a : V) (ha : a ≠ 0) : Function.Surjective F := by
  classical
  let j : I := Classical.choice inferInstance
  have hn : F a j ≠ 0 := by
    intro h
    apply ha
    apply hF
    ext i
    simpa only [Subsingleton.elim i j, map_zero, Pi.zero_apply] using h
  intro y
  refine ⟨(y j / F a j) • a, ?_⟩
  ext i
  rw [map_smul]
  change (y j / F a j) * F a i = y i
  rw [Subsingleton.elim i j, div_mul_cancel₀ _ hn]

end HodgeLean.Foundations.QuotientDuality
