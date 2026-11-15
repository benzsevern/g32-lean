import HodgeLean.Foundations.Program.SchoenTowerT11bConnectedCoverTransport

/-! Finite preconnected covers of actual Boolean polynomial realizations.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A connected cylindrical base region with actual fiber coordinates gives a finite preconnected cover of the original restricted realization.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, connected cylindrical lifting step. -/
theorem s2v_t11b_restricted_formula_preconnected_cover {n : ℕ}
    (f : s2v_t11b_Formula (n + 1)) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsPreconnected K)
    (hchart : ∀ a : K, Nonempty
      (({x : ℝ | WithLp.toLp 2 (Fin.cons x (fun v => a.val v)) ∈ f.realize} × K) ≃ₜ
        {z : K × ℝ | WithLp.toLp 2 (Fin.cons z.2 (fun v => z.1.val v)) ∈ f.realize})) :
    ∃ m : ℕ, ∃ V : Fin m → Set (EuclideanSpace ℝ (Fin (n + 1))),
      (∀ i, IsPreconnected (V i) ∧ V i ⊆ {y | y ∈ f.realize ∧ WithLp.toLp 2 (fun v => y v.succ) ∈ K}) ∧
      ∀ y, y ∈ f.realize → WithLp.toLp 2 (fun v => y v.succ) ∈ K → ∃ i, y ∈ V i := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨F⟩ := hchart ⟨a, ha⟩
    obtain ⟨m, U, hU, hcover⟩ := s2v_t11b_slice_finite_preconnected_cover f a
    let A := s2v_t11b_euclideanSetBaseChart f.realize K
    obtain ⟨V, hV, hVcover⟩ := s2v_t11b_product_chart_preconnected_cover _ _ K hK
      (F.trans A.symm) U hU hcover
    exact ⟨m, V, hV, fun y hy hk => hVcover y ⟨hy, hk⟩⟩
  · refine ⟨0, Fin.elim0, (fun i => Fin.elim0 i), ?_⟩
    intro y hy hk
    exact (hne ⟨_, hk⟩).elim

/-- Every Boolean polynomial realization has a finite cover by preconnected subsets of that realization.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite connected cover induction step. -/
theorem s2v_t11b_formula_finite_preconnected_cover (n : ℕ) (f : s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ U : Fin m → Set (EuclideanSpace ℝ (Fin n)),
      (∀ i, IsPreconnected (U i) ∧ U i ⊆ f.realize) ∧
      ∀ x, x ∈ f.realize → ∃ i, x ∈ U i := by
  classical
  induction n with
  | zero =>
    refine ⟨1, fun _ => f.realize, ?_, fun x hx => ⟨0, hx⟩⟩
    intro i
    exact ⟨(show f.realize.Subsingleton from fun _ _ _ _ => Subsingleton.elim _ _).isPreconnected,
      Set.Subset.rfl⟩
  | succ n ih =>
    obtain ⟨m, c, hc, hcharts⟩ := s2v_t11b_formula_finite_subregion_charts f
    choose k U hU hUcover using fun i => ih (c i)
    have hlift : ∀ i (j : Fin (k i)), ∃ l : ℕ,
        ∃ V : Fin l → Set (EuclideanSpace ℝ (Fin (n + 1))),
          (∀ q, IsPreconnected (V q) ∧ V q ⊆ {y | y ∈ f.realize ∧
            WithLp.toLp 2 (fun v => y v.succ) ∈ U i j}) ∧
          ∀ y, y ∈ f.realize → WithLp.toLp 2 (fun v => y v.succ) ∈ U i j → ∃ q, y ∈ V q := by
      intro i j
      apply s2v_t11b_restricted_formula_preconnected_cover f (U i j) (hU i j).1
      intro a
      obtain ⟨F, _⟩ := hcharts i (U i j) (hU i j).2 (hU i j).1 a
      exact ⟨F⟩
    choose l V hV hVcover using hlift
    let J := (i : Fin m) × (j : Fin (k i)) × Fin (l i j)
    let E := Fintype.equivFin J
    refine ⟨Fintype.card J, fun q => V (E.symm q).1 (E.symm q).2.1 (E.symm q).2.2, ?_, ?_⟩
    · intro q
      exact ⟨(hV _ _ _).1, fun x hx => ((hV _ _ _).2 hx).1⟩
    · intro x hx
      obtain ⟨i, hi⟩ := hc (WithLp.toLp 2 (fun v => x v.succ))
      obtain ⟨j, hj⟩ := hUcover i _ hi
      obtain ⟨q, hq⟩ := hVcover i j x hx hj
      refine ⟨E ⟨i, j, q⟩, ?_⟩
      change x ∈ V (E.symm (E (⟨i, j, q⟩ : J))).1
        (E.symm (E (⟨i, j, q⟩ : J))).2.1 (E.symm (E (⟨i, j, q⟩ : J))).2.2
      rw [E.symm_apply_apply]
      exact hq

end HodgeLean.Foundations.Program
