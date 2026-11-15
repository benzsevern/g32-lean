import HodgeLean.Foundations.Program.SchoenTowerHardtCad5CoefficientField
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5IndependentBoxes

/-! Polynomial equations on thin Boolean sets and their ambient limit sets. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_polynomial_zero_interior {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    interior {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) p = 0} = ∅ := by
  obtain ⟨K, hK, hcoeff⟩ := s2v_hardt_cad5_formula_coefficient_field
    (fun _ : Fin 1 => n) (fun _ => s2v_t11b_Formula.nonneg p)
  letI := hK
  obtain ⟨q, hq⟩ := hcoeff 0 p (Finset.mem_singleton_self p)
  by_contra h
  obtain ⟨x, hx, hxi⟩ := s2v_hardt_cad5_independent_open_point K _ isOpen_interior
    (Set.nonempty_iff_ne_empty.mpr h)
  have hz : x ∈ {x : EuclideanSpace ℝ (Fin n) |
      MvPolynomial.eval (fun i => x i) p = 0} := interior_subset hx
  have hqa : MvPolynomial.aeval (fun i => x i) q = 0 := by
    change MvPolynomial.eval₂ (algebraMap K ℝ) (fun i => x i) q = 0
    rw [MvPolynomial.eval₂_eq_eval_map]
    change MvPolynomial.eval (fun i => x i) (MvPolynomial.map K.subtype q) = 0
    rw [hq]
    exact hz
  have hq0 := hxi.eq_zero_of_aeval_eq_zero q hqa
  apply hp
  rw [← hq, hq0, map_zero]

theorem s2v_hardt_cad5_thin_boolean_polynomial_limit {n : ℕ}
    (f : s2v_t11b_Formula n) (hi : interior f.realize = ∅) :
    ∃ p : MvPolynomial (Fin n) ℝ, p ≠ 0 ∧
      closure f.realize ⊆ {x | MvPolynomial.eval (fun i => x i) p = 0} := by
  classical
  let A := f.atoms.filter (fun p => p ≠ 0)
  let p : MvPolynomial (Fin n) ℝ := ∏ q ∈ A, q
  have hp : p ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hs : f.realize ⊆ {x | MvPolynomial.eval (fun i => x i) p = 0} := by
    intro x hx
    have hxi : x ∉ interior f.realize := by rw [hi]; exact Set.notMem_empty x
    obtain ⟨q, hq, hqn, hqz⟩ := s2v_t11b_boundary_active_atom f x hx hxi
    change MvPolynomial.eval (fun i => x i) p = 0
    dsimp only [p]
    rw [map_prod]
    exact Finset.prod_eq_zero_iff.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hqn⟩, hqz⟩
  have hc : IsClosed {x : EuclideanSpace ℝ (Fin n) |
      MvPolynomial.eval (fun i => x i) p = 0} :=
    isClosed_eq (p.continuous_eval.comp (PiLp.continuous_ofLp 2 _)) continuous_const
  exact ⟨p, hp, closure_minimal hs hc⟩

theorem s2v_hardt_cad5_thin_boolean_limit_interior {n : ℕ}
    (f : s2v_t11b_Formula n) (hi : interior f.realize = ∅) :
    interior (closure f.realize) = ∅ := by
  obtain ⟨p, hp, hs⟩ := s2v_hardt_cad5_thin_boolean_polynomial_limit f hi
  have h := interior_mono hs
  rw [s2v_hardt_cad5_polynomial_zero_interior p hp] at h
  exact Set.subset_empty_iff.mp h

end HodgeLean.Foundations.Program
