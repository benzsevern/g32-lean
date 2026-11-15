import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairKernelAction

/-! Normalized Hermitian coordinate kernels fix their representative vectors.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.WitnessSelection.StageTwo

/-- A nonzero vector is fixed by its normalized rank-one kernel.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projectiveKernel_self {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (hv : v ≠ 0) (i : ι) :
    (∑ j, s2e_pair_projectiveKernel v i j * v j) = v i := by
  have hmass : (∑ j, star (v j) * v j) = (s2e_pair_vectorMass v : ℂ) := by
    change (∑ j, star (v j) * v j) = Complex.ofRealHom (∑ j, Complex.normSq (v j))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact Complex.normSq_eq_conj_mul_self.symm
  have hne : (s2e_pair_vectorMass v : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (s2e_pair_vectorMass_pos v hv))
  rw [s2e_pair_projectiveKernel_action, hmass, div_self hne, one_mul]

end HodgeLean.WitnessSelection.StageTwo
