import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairKernelRationalCoordinates
import HodgeLean.Foundations.Program.SchoenTowerHardtCad3FormulaTools
import HodgeLean.Foundations.Program.SchoenTowerT11bGraph

/-! Exact Boolean graphs of normalized Hermitian real coordinates.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection.StageTwo

/-- The real coordinate kernel graph has an exact Boolean description on its nonzero-vector domain.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_kernel_graph_formula {ι : Type*} [Fintype ι] {n : ℕ}
    (r s : ι → MvPolynomial (Fin n) ℝ)
    (idx : Fin (Fintype.card ((ι × ι) ⊕ (ι × ι))) → Fin n) :
    let v : (Fin n → ℝ) → ι → ℂ := fun x i =>
      (MvPolynomial.eval x (r i) : ℂ) + (MvPolynomial.eval x (s i) : ℂ) * Complex.I
    ∃ f : s2v_t11b_Formula n, ∀ x : EuclideanSpace ℝ (Fin n),
      x ∈ f.realize ↔ v (fun j => x j) ≠ 0 ∧
        ∀ k, x (idx k) = s2e_pair_complexRealCoordinates
          (fun a : ι × ι => s2e_pair_projectiveKernel (v (fun j => x j)) a.1 a.2) k := by
  classical
  let v : (Fin n → ℝ) → ι → ℂ := fun x i =>
    (MvPolynomial.eval x (r i) : ℂ) + (MvPolynomial.eval x (s i) : ℂ) * Complex.I
  obtain ⟨M, P, hM, hP⟩ := s2e_pair_kernel_rational_coordinates r s
  obtain ⟨G, hG⟩ := s2v_hardt_cad3_finite_inter (fun k =>
    s2v_t11b_zeroFormula (MvPolynomial.X (idx k) * M - P k))
  refine ⟨.inter (.compl (.nonneg (-M))) G, ?_⟩
  intro x
  have hm : 0 < MvPolynomial.eval (fun j => x j) M ↔ v (fun j => x j) ≠ 0 := by
    rw [hM]
    constructor
    · intro h hz
      change 0 < s2e_pair_vectorMass (v (fun j => x j)) at h
      rw [hz] at h
      simpa only [s2e_pair_vectorMass, Pi.zero_apply, Complex.normSq_zero,
        Finset.sum_const_zero, lt_self_iff_false] using h
    · exact s2e_pair_vectorMass_pos _
  change (¬0 ≤ MvPolynomial.eval (fun j => x j) (-M)) ∧ x ∈ G.realize ↔ _
  rw [map_neg, neg_nonneg, not_le, hG]
  simp_rw [s2v_t11b_realize_zeroFormula, map_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, sub_eq_zero]
  constructor
  · rintro ⟨hx, he⟩
    refine ⟨hm.mp hx, ?_⟩
    intro k
    rw [hP]
    exact (eq_div_iff (ne_of_gt hx)).mpr (he k)
  · rintro ⟨hx, he⟩
    have hpos := hm.mpr hx
    refine ⟨hpos, ?_⟩
    intro k
    have hk := he k
    rw [hP] at hk
    exact (eq_div_iff (ne_of_gt hpos)).mp hk

end HodgeLean.WitnessSelection.StageTwo
