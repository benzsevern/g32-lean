import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveKernel

/-! Continuity of normalized Hermitian kernels away from the zero vector.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.WitnessSelection.StageTwo

/-- Normalized Hermitian kernels vary continuously on nonzero coordinate vectors.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projectiveKernel_continuous {ι : Type*} [Fintype ι] :
    Continuous (fun v : {v : ι → ℂ // v ≠ 0} => s2e_pair_projectiveKernel v.val) := by
  have hc (i : ι) : Continuous (fun v : {v : ι → ℂ // v ≠ 0} => v.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  have hm : Continuous (fun v : {v : ι → ℂ // v ≠ 0} => s2e_pair_vectorMass v.val) :=
    continuous_finsetSum Finset.univ (fun i _ => Complex.continuous_normSq.comp (hc i))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((hc i).mul (hc j).star).div (Complex.continuous_ofReal.comp hm) (fun v => by
    exact_mod_cast (ne_of_gt (s2e_pair_vectorMass_pos v.val v.property)))

end HodgeLean.WitnessSelection.StageTwo
