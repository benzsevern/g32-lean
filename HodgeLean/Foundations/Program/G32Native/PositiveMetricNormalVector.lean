import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Basic.Real.Basic

/-! # Unique normal vectors for a positive metric and a surjective quotient

The orthogonal complement of the actual kernel determines the representative.
No norm on the quotient and no chosen replacement fibre are required.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Function
namespace HodgeLean.Foundations.TubularEuler

/-- A positive symmetric real bilinear form chooses the unique orthogonal
representative of any value of a surjective finite-dimensional linear map.
Source: Mathlib, `LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint`;
Lee, Introduction to Smooth Manifolds, second edition, normal spaces in the
proof of Theorem 6.24.
HC no distance; AV milestone no distance. -/
theorem positiveMetric_normal_vector_exists_unique
    {E N : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup N] [Module ℝ N]
    (G : LinearMap.BilinForm ℝ E)
    (hsym : ∀ u v, G u v = G v u)
    (hpos : ∀ u, u ≠ 0 → 0 < G u u)
    (T : E →ₗ[ℝ] N) (hT : Surjective T) (n : N) :
    ∃! v : E, T v = n ∧ ∀ w, T w = 0 → G v w = 0 := by
  have hrefl : G.IsRefl := fun u v h => (hsym v u).trans h
  have hdis : Disjoint T.ker (G.orthogonal T.ker) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hvO
    by_contra hne
    exact (ne_of_gt (hpos v hne)) (hvO v hv)
  have hcompl : IsCompl T.ker (G.orthogonal T.ker) :=
    (G.isCompl_orthogonal_iff_disjoint hrefl).mpr hdis
  obtain ⟨v₀, hv₀⟩ := hT n
  obtain ⟨w, z, hw, hz, heq⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.mp hcompl.codisjoint v₀
  have hzT : T z = n := by
    have h := congrArg T heq
    rw [map_add, show T w = 0 from hw, zero_add, hv₀] at h
    exact h
  have hzO : ∀ w, T w = 0 → G z w = 0 := by
    intro w hw
    rw [hsym]
    exact hz w hw
  refine ⟨z, ⟨hzT, hzO⟩, ?_⟩
  intro v hv
  apply sub_eq_zero.mp
  have hk : T (v - z) = 0 := by rw [map_sub, hv.1, hzT, sub_self]
  by_contra hne
  have hp := hpos (v - z) hne
  have hzero : G (v - z) (v - z) = 0 := by
    rw [G.map_sub v z, LinearMap.sub_apply, hv.2 _ hk, hzO _ hk, sub_self]
  exact (ne_of_gt hp) hzero

#print axioms positiveMetric_normal_vector_exists_unique

end HodgeLean.Foundations.TubularEuler
