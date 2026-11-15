import Mathlib.LinearAlgebra.Eigenspace.Minpoly

namespace HodgeLean.Foundations.Program

/-- An injective intertwiner onto a polynomial kernel identifies every root eigenspace. -/
theorem s4_eigenspace_map_of_polynomial_range {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (F : V →ₗ[K] W) (T : Module.End K V) (A : Module.End K W) (P : Polynomial K)
    (hF : Function.Injective F) (hFA : ∀ x, A (F x) = F (T x))
    (hrange : LinearMap.range F = LinearMap.ker (Polynomial.aeval A P))
    (μ : K) (hμ : P.IsRoot μ) :
    (Module.End.eigenspace T μ).map F = Module.End.eigenspace A μ := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    rw [hFA, Module.End.mem_eigenspace_iff.mp hv, map_smul]
  · intro w hw
    have hAw := Module.End.mem_eigenspace_iff.mp hw
    have hp : Polynomial.aeval A P w = 0 := by
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul hAw, hμ, zero_smul]
    have hpk : w ∈ LinearMap.ker (Polynomial.aeval A P) := hp
    obtain ⟨v, rfl⟩ := hrange.symm ▸ hpk
    refine ⟨v, Module.End.mem_eigenspace_iff.mpr ?_, rfl⟩
    apply hF
    rw [← hFA, hAw, map_smul]

end HodgeLean.Foundations.Program
