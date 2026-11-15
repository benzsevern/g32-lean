import HodgeLean.Foundations.Program.SchoenTowerT11bFiniteComponents

/-! Finite disjoint connected refinements of actual Boolean parameter covers.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite Boolean cover has a finite disjoint connected refinement inside its actual pieces.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, connected Boolean cover refinement step. -/
theorem s2v_t11b_finite_connected_refinement {n m : ℕ} (c : Fin m → s2v_t11b_Formula n)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin n), ∃ i, x ∈ (c i).realize) :
    ∃ l : ℕ, ∃ K : Fin l → Set (EuclideanSpace ℝ (Fin n)),
      (∀ q, IsConnected (K q)) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ∃ q, x ∈ K q) ∧
      Pairwise (fun q r => Disjoint (K q) (K r)) ∧
      ∀ q, ∃ i, K q ⊆ (c i).realize := by
  classical
  let R := s2v_t11b_refinementFormula c
  choose k U hU hUcover hdisj hcomp using fun s : Fin m → Bool =>
    s2v_t11b_formula_finite_component_partition (R s)
  let J := (s : Fin m → Bool) × Fin (k s)
  let E := Fintype.equivFin J
  let K : Fin (Fintype.card J) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun q => U (E.symm q).1 (E.symm q).2
  refine ⟨Fintype.card J, K, fun q => (hU _ _).1, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨s, hs, _⟩ := s2v_t11b_refinement_partition c x
    obtain ⟨j, hj⟩ := hUcover s x hs
    refine ⟨E ⟨s, j⟩, ?_⟩
    change x ∈ U (E.symm (E (⟨s, j⟩ : J))).1 (E.symm (E (⟨s, j⟩ : J))).2
    rw [E.symm_apply_apply]
    exact hj
  · intro q r hqr
    apply Set.disjoint_left.mpr
    intro x hxq hxr
    have hq : x ∈ (R (E.symm q).1).realize := (hU _ _).2 hxq
    have hr : x ∈ (R (E.symm r).1).realize := (hU _ _).2 hxr
    obtain ⟨s, hs, huniq⟩ := s2v_t11b_refinement_partition c x
    have he : (E.symm q).1 = (E.symm r).1 := (huniq _ hq).trans (huniq _ hr).symm
    have hd : ∀ a b : J, a.1 = b.1 → x ∈ U a.1 a.2 → x ∈ U b.1 b.2 → a = b := by
      rintro ⟨s, i⟩ ⟨t, j⟩ hst hxi hxj
      dsimp at hst hxi hxj ⊢
      subst t
      have hij : i = j := by
        by_contra hij
        exact Set.disjoint_left.mp (hdisj s hij) hxi hxj
      subst j
      rfl
    exact hqr (E.symm.injective (hd _ _ he hxq hxr))
  · intro q
    obtain ⟨x, hx⟩ := (hU (E.symm q).1 (E.symm q).2).1.nonempty
    obtain ⟨i, hi⟩ := hcover x
    have hs := (s2v_t11b_realize_refinementFormula c (E.symm q).1 x).mp ((hU _ _).2 hx)
    refine ⟨i, ?_⟩
    intro y hy
    exact ((s2v_t11b_realize_refinementFormula c (E.symm q).1 y).mp ((hU _ _).2 hy) i).mp
      ((hs i).mpr hi)

end HodgeLean.Foundations.Program
