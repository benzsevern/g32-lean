import HodgeLean.Foundations.Program.SchoenCycleU1SupportSeparation

/-! # Simultaneous nonvanishing of finitely many linear functionals -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Finitely many nonzero complex linear functionals are simultaneously
nonzero on a single vector, with no finite-dimensionality premise.
Source: Hartshorne, Algebraic Geometry, I.1, avoidance of finitely many hyperplanes. -/
theorem s2e_u1_exists_nonzero_linear_functionals
    {ι : Type} {V : Type*} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    (L : ι → V →ₗ[ℂ] ℂ) (hL : ∀ i, ∃ v, L i v ≠ 0) :
    ∃ v : V, ∀ i, L i v ≠ 0 := by
  classical
  choose v hv using hL
  have hG (i : ι) : a3r_Generic {a : ι → ℂ | (∑ j, a j * L i (v j)) ≠ 0} := by
    let G : MvPolynomial ι ℂ := ∑ j, C (L i (v j)) * X j
    have hn : G ≠ 0 := by
      intro h
      have hh := congrArg (MvPolynomial.eval (fun j => if j = i then 1 else 0)) h
      have hz : L i (v i) = 0 := by simpa [G] using hh
      exact hv i hz
    refine (a3r_generic_of_ne_zero G hn).mono ?_
    intro a ha
    simpa [G, mul_comm] using ha
  obtain ⟨a, ha⟩ := (a3r_generic_iInter_fintype _ hG).nonempty
  refine ⟨∑ j, a j • v j, ?_⟩
  intro i
  simpa only [Set.mem_setOf_eq, map_sum, map_smul, smul_eq_mul] using ha i

end HodgeLean.Foundations.Program
