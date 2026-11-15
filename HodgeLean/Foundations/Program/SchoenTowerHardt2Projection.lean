import HodgeLean.Foundations.Program.SchoenTowerHardt1

/-! Quantified polynomial operations. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- One existential spatial coordinate has a Boolean parameter description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1. -/
theorem s2v_hardt2_project_coordinate {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ d : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ d.realize ↔ ∃ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize := by
  classical
  obtain ⟨m, c, hc, hcharts⟩ := s2v_t11b_euclidean_finite_subregion_charts f
  obtain ⟨l, d, hd, hcover, _, hsub⟩ :=
    s2v_hardt1_connected_boolean_refinement c hc
  let D : Fin l → s2v_t11b_Formula n := fun q =>
    if (∃ a ∈ (d q).realize, ∃ x : ℝ,
      WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize) then d q else .compl (.nonneg 0)
  obtain ⟨g, hg⟩ := s2v_t11b_finite_union_formula D
  refine ⟨g, ?_⟩
  intro a
  rw [hg]
  constructor
  · rintro ⟨q, hq⟩
    by_cases hA : ∃ b ∈ (d q).realize, ∃ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => b i)) ∈ f.realize
    · have ha : a ∈ (d q).realize := by simpa [D, hA] using hq
      obtain ⟨b, hb, x, hx⟩ := hA
      obtain ⟨i, hi⟩ := hsub q
      obtain ⟨e, he⟩ := hcharts i (d q).realize hi (hd q).isPreconnected ⟨b, hb⟩
      let y : {y : EuclideanSpace ℝ (Fin (n + 1)) |
          y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) ∈ (d q).realize} :=
        ⟨WithLp.toLp 2 (Fin.cons x (fun v => b v)), hx, hb⟩
      let z := e.symm ((e y).1, ⟨a, ha⟩)
      have hz : WithLp.toLp 2 (fun v => z.val v.succ) = a := by
        have h := he z
        rw [show e z = ((e y).1, ⟨a, ha⟩) from e.apply_symm_apply _] at h
        exact h.symm
      refine ⟨z.val 0, ?_⟩
      have heta : WithLp.toLp 2 (Fin.cons (z.val 0) (fun v => a v)) = z.val := by
        ext v
        refine Fin.cases (by rfl) (fun j => ?_) v
        exact (congrArg (fun t : EuclideanSpace ℝ (Fin n) => t j) hz).symm
      rw [heta]
      exact z.property.1
    · simpa [D, hA, s2v_t11b_Formula.realize] using hq
  · rintro ⟨x, hx⟩
    obtain ⟨q, hq⟩ := hcover a
    have hA : ∃ b ∈ (d q).realize, ∃ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => b i)) ∈ f.realize := ⟨a, hq, x, hx⟩
    exact ⟨q, by simpa [D, hA] using hq⟩


/-- Universal elimination follows by taking the complement of the existential complement.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, Boolean consequence. -/
theorem s2v_hardt2_forall_coordinate {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ d : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ d.realize ↔ ∀ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize := by
  classical
  obtain ⟨d, hd⟩ := s2v_hardt2_project_coordinate (.compl f)
  refine ⟨.compl d, ?_⟩
  intro a
  change (¬ a ∈ d.realize) ↔ _
  rw [hd]
  simp only [s2v_t11b_Formula.realize, Set.mem_compl_iff, not_exists, not_not]

#print axioms s2v_hardt2_project_coordinate
#print axioms s2v_hardt2_forall_coordinate

end HodgeLean.Foundations.Program
