import HodgeLean.Foundations.Program.SchoenTowerT11bRootCuts

/-! Finite connected covers of one-dimensional Boolean polynomial realizations.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A root-cut piece intersected with a Boolean realization is either the entire piece or empty, hence preconnected.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, connected one-dimensional piece step. -/
theorem s2v_t11b_line_selected_cut_preconnected {n k : ℕ} (f : s2v_t11b_Formula n)
    (d : Fin k → ℝ) (hd : ∀ r ∈ f.exceptionalValues, ∃ i, d i = r)
    (s : Fin (k + k) → Bool) :
    IsPreconnected {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈
      (s2v_t11b_refinementFormula (s2v_t11b_rootCutTests d) s).realize ∧
      WithLp.toLp 2 (fun _ : Fin n => t) ∈ f.realize} := by
  let K : Set ℝ := {t | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈
    (s2v_t11b_refinementFormula (s2v_t11b_rootCutTests d) s).realize}
  have hc : ∀ a ∈ K, ∀ b ∈ K, WithLp.toLp 2 (fun _ : Fin n => a) ∈ f.realize ↔
      WithLp.toLp 2 (fun _ : Fin n => b) ∈ f.realize := by
    intro a ha b hb
    have hsame : ∀ j, WithLp.toLp 2 (fun _ : Fin 1 => a) ∈ (s2v_t11b_rootCutTests d j).realize ↔
        WithLp.toLp 2 (fun _ : Fin 1 => b) ∈ (s2v_t11b_rootCutTests d j).realize := fun j =>
      ((s2v_t11b_realize_refinementFormula _ s _).mp ha j).symm.trans
        ((s2v_t11b_realize_refinementFormula _ s _).mp hb j)
    apply s2v_t11b_formula_constant_on_root_cuts f a b
    intro r hr
    obtain ⟨i, hi⟩ := hd r hr
    exact ⟨by simpa only [s2v_t11b_rootCutTests_upper, hi] using hsame (Fin.natAdd k i),
      by simpa only [s2v_t11b_rootCutTests_lower, hi] using hsame (i.castAdd k)⟩
  by_cases h : ∃ a ∈ K, WithLp.toLp 2 (fun _ : Fin n => a) ∈ f.realize
  · obtain ⟨a, ha, hf⟩ := h
    have he : {t : ℝ | t ∈ K ∧ WithLp.toLp 2 (fun _ : Fin n => t) ∈ f.realize} = K := by
      ext t
      exact ⟨And.left, fun ht => ⟨ht, (hc a ha t ht).mp hf⟩⟩
    change IsPreconnected {t : ℝ | t ∈ K ∧ WithLp.toLp 2 (fun _ : Fin n => t) ∈ f.realize}
    rw [he]
    exact s2v_t11b_root_cut_piece_preconnected d s
  · have he : {t : ℝ | t ∈ K ∧ WithLp.toLp 2 (fun _ : Fin n => t) ∈ f.realize} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro ht hf
      exact h ⟨t, ht, hf⟩
    change IsPreconnected {t : ℝ | t ∈ K ∧ WithLp.toLp 2 (fun _ : Fin n => t) ∈ f.realize}
    rw [he]
    exact isPreconnected_empty


/-- A Boolean polynomial realization along the real line has a finite cover by preconnected subsets of that realization.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite connected line cover step. -/
theorem s2v_t11b_line_finite_preconnected_cover {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ U : Fin m → Set ℝ,
      (∀ i, IsPreconnected (U i) ∧ U i ⊆ {t | WithLp.toLp 2 (fun _ : Fin n => t) ∈ f.realize}) ∧
      ∀ t, WithLp.toLp 2 (fun _ : Fin n => t) ∈ f.realize → ∃ i, t ∈ U i := by
  classical
  let R := {r : ℝ // r ∈ f.exceptionalValues}
  let k := Fintype.card R
  let E : Fin k ≃ R := (Fintype.equivFin R).symm
  let d : Fin k → ℝ := fun i => (E i).val
  have hd : ∀ r ∈ f.exceptionalValues, ∃ i, d i = r := by
    intro r hr
    exact ⟨E.symm ⟨r, hr⟩, congrArg Subtype.val (E.apply_symm_apply ⟨r, hr⟩)⟩
  let J := (Fintype.equivFin (Fin (k + k) → Bool)).symm
  let U : (Fin (k + k) → Bool) → Set ℝ := fun s => {t |
    WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (s2v_t11b_refinementFormula (s2v_t11b_rootCutTests d) s).realize ∧
    WithLp.toLp 2 (fun _ : Fin n => t) ∈ f.realize}
  refine ⟨Fintype.card (Fin (k + k) → Bool), fun i => U (J i), ?_, ?_⟩
  · intro i
    exact ⟨s2v_t11b_line_selected_cut_preconnected f d hd (J i), fun _ ht => ht.2⟩
  · intro t ht
    obtain ⟨s, hs, _⟩ := s2v_t11b_refinement_partition (s2v_t11b_rootCutTests d)
      (WithLp.toLp 2 (fun _ : Fin 1 => t))
    refine ⟨J.symm s, ?_⟩
    change t ∈ U (J (J.symm s))
    rw [J.apply_symm_apply]
    exact ⟨hs, ht⟩


/-- Every actual one-coordinate fiber of a Boolean formula has a finite preconnected cover.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, connected fiber cover step. -/
theorem s2v_t11b_slice_finite_preconnected_cover {n : ℕ}
    (f : s2v_t11b_Formula (n + 1)) (a : EuclideanSpace ℝ (Fin n)) :
    ∃ m : ℕ, ∃ U : Fin m → Set ℝ,
      (∀ i, IsPreconnected (U i) ∧ U i ⊆ {x | WithLp.toLp 2 (Fin.cons x (fun v => a v)) ∈ f.realize}) ∧
      ∀ x, WithLp.toLp 2 (Fin.cons x (fun v => a v)) ∈ f.realize → ∃ i, x ∈ U i := by
  let σ : Fin (n + 1) → MvPolynomial (Fin 1) ℝ := Fin.cons (MvPolynomial.X 0) (fun i => MvPolynomial.C (a i))
  have he : ∀ x : ℝ, WithLp.toLp 2 (fun _ : Fin 1 => x) ∈ (f.subst σ).realize ↔
      WithLp.toLp 2 (Fin.cons x (fun v => a v)) ∈ f.realize := by
    intro x
    rw [s2v_t11b_realize_subst]
    have hv : (fun i => MvPolynomial.eval (fun _ : Fin 1 => x) (σ i)) = Fin.cons x (fun v => a v) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact MvPolynomial.eval_X _
      · exact MvPolynomial.eval_C _
    rw [hv]
  obtain ⟨m, U, hU, hcover⟩ := s2v_t11b_line_finite_preconnected_cover (f.subst σ)
  refine ⟨m, U, fun i => ⟨(hU i).1, fun x hx => (he x).mp ((hU i).2 hx)⟩, ?_⟩
  intro x hx
  exact hcover x ((he x).mpr hx)

end HodgeLean.Foundations.Program
