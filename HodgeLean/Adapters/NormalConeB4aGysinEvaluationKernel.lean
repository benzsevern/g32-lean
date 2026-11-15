import Mathlib.RingTheory.Ideal.Maps

noncomputable section
namespace HodgeLean.Adapters

/-- Scalar-valued algebra evaluations with the same kernel are equal. -/
theorem a3b4a_gysin_evaluation_eq_of_ker_eq
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (w w' : R →ₐ[k] k) (hk : RingHom.ker w = RingHom.ker w') : w = w' := by
  apply AlgHom.ext
  intro t
  have ht : w (t - algebraMap k R (w' t)) = 0 := by
    change t - algebraMap k R (w' t) ∈ RingHom.ker w
    rw [hk]
    change w' (t - algebraMap k R (w' t)) = 0
    simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  rw [map_sub, w.commutes, Algebra.algebraMap_self_apply] at ht
  exact sub_eq_zero.mp ht

end HodgeLean.Adapters
