import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Transverse equivalences from the actual quotient section

A section of a quotient remains an equivalence after any surjective
transverse projection with the same kernel.
-/

noncomputable section
namespace HodgeLean.Foundations.TubularEuler

theorem quotient_section_transverse_bijective
    {K E P N : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup P] [Module K P]
    [AddCommGroup N] [Module K N]
    (T : E →ₗ[K] P) (L : P →ₗ[K] E) (B : E →ₗ[K] N)
    (hL : ∀ u, T (L u) = u) (hker : B.ker = T.ker)
    (hB : Function.Surjective B) : Function.Bijective (B.comp L) := by
  constructor
  · intro u v huv
    change B (L u) = B (L v) at huv
    have hz : L (u - v) ∈ B.ker := by
      change B (L (u - v)) = 0
      rw [map_sub, map_sub, huv, sub_self]
    rw [hker] at hz
    change T (L (u - v)) = 0 at hz
    rw [hL] at hz
    exact sub_eq_zero.mp hz
  · intro n
    obtain ⟨w, hw⟩ := hB n
    refine ⟨T w, ?_⟩
    have hz : L (T w) - w ∈ T.ker := by
      change T (L (T w) - w) = 0
      rw [map_sub, hL, sub_self]
    rw [← hker] at hz
    change B (L (T w) - w) = 0 at hz
    rw [map_sub] at hz
    exact (sub_eq_zero.mp hz).trans hw

#print axioms quotient_section_transverse_bijective

theorem quotient_section_transverse_equiv
    {K E P N : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [AddCommGroup E] [Module K E]
    [NormedAddCommGroup P] [NormedSpace K P] [FiniteDimensional K P]
    [NormedAddCommGroup N] [NormedSpace K N] [FiniteDimensional K N]
    (T : E →ₗ[K] P) (L : P →ₗ[K] E) (B : E →ₗ[K] N)
    (hL : ∀ u, T (L u) = u) (hker : B.ker = T.ker)
    (hB : Function.Surjective B) :
    ∃ A : P ≃L[K] N, ∀ u, A u = B (L u) := by
  let A := LinearEquiv.ofBijective (B.comp L)
    (quotient_section_transverse_bijective T L B hL hker hB)
  exact ⟨A.toContinuousLinearEquiv, fun _ => rfl⟩

#print axioms quotient_section_transverse_equiv
end HodgeLean.Foundations.TubularEuler
