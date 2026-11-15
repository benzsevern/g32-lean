import HodgeLean.Foundations.Program.SchoenTowerHardt1Cells

/-! Finite covers by preconnected Boolean cylindrical pieces. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every Boolean realization has a finite cover by preconnected Boolean realizations.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, preconnected decomposition step. -/
theorem s2v_hardt1_boolean_preconnected_cover (n : ℕ) (f : s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ d : Fin m → s2v_t11b_Formula n,
      (∀ i, IsPreconnected (d i).realize ∧ (d i).realize ⊆ f.realize) ∧
      ∀ x ∈ f.realize, ∃ i, x ∈ (d i).realize := by
  classical
  induction n with
  | zero =>
    refine ⟨1, fun _ => f, ?_, fun x hx => ⟨0, hx⟩⟩
    intro i
    exact ⟨(show f.realize.Subsingleton from fun _ _ _ _ => Subsingleton.elim _ _).isPreconnected,
      Set.Subset.rfl⟩
  | succ n ih =>
    obtain ⟨r, g, hgsub, hgcover, hginterval⟩ := s2v_hardt1_interval_formula_cover f
    choose m c hc hcharts using fun s => s2v_t11b_formula_finite_subregion_charts (g s)
    choose k d hd hdcover using fun s i => ih (c s i)
    let J := (s : Fin r) × (i : Fin (m s)) × Fin (k s i)
    let E := Fintype.equivFin J
    let D : J → s2v_t11b_Formula (n + 1) := fun q =>
      .inter (g q.1) (s2v_hardt1_rename Fin.succ (d q.1 q.2.1 q.2.2))
    have hD : ∀ q : J, (D q).realize = {y | y ∈ (g q.1).realize ∧
        WithLp.toLp 2 (fun v => y v.succ) ∈ (d q.1 q.2.1 q.2.2).realize} := by
      intro q
      ext y
      exact and_congr Iff.rfl (s2v_hardt1_realize_rename _ _ _)
    refine ⟨_, fun q => D (E.symm q), ?_, ?_⟩
    · intro q
      refine ⟨?_, fun y hy => hgsub _ hy.1⟩
      rw [hD]
      apply s2v_hardt1_interval_lift _ _ (hd _ _ _).1
      · intro a
        exact hginterval _ a.val
      · intro a
        obtain ⟨F, _⟩ := hcharts (E.symm q).1 (E.symm q).2.1 _
          (hd _ _ _).2 (hd _ _ _).1 a
        exact ⟨F⟩
    · intro x hx
      obtain ⟨s, hs⟩ := hgcover x hx
      obtain ⟨i, hi⟩ := hc s (WithLp.toLp 2 (fun v => x v.succ))
      obtain ⟨j, hj⟩ := hdcover s i _ hi
      refine ⟨E ⟨s, i, j⟩, ?_⟩
      change x ∈ (D (E.symm (E (⟨s, i, j⟩ : J)))).realize
      rw [E.symm_apply_apply, hD]
      exact ⟨hs, hj⟩

end HodgeLean.Foundations.Program
