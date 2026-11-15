import HodgeLean.Foundations.Program.SchoenTowerT11bConnectedRefinement
import HodgeLean.Foundations.Program.SchoenTowerHardt1Partition

/-! Boolean descriptions of actual connected components and their finite refinements.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Each actual component of a polynomial Boolean realization has a polynomial Boolean description.
Source: Coste, Real Algebraic Sets (2005), Proposition 1.6, semialgebraicity assertion. -/
theorem s2v_hardt1_component_formula_aux {n : ℕ} (f : s2v_t11b_Formula n)
    (x : f.realize) :
    ∃ c : s2v_t11b_Formula n,
      c.realize = Subtype.val '' connectedComponent x := by
  obtain ⟨m, d, hd, hcover⟩ := s2v_hardt1_boolean_preconnected_cover n f
  exact s2v_hardt1_extract_component f d hd hcover x

/-- A finite Boolean cover has a disjoint connected refinement consisting of Boolean realizations.
Source: Coste, Real Algebraic Sets (2005), Proposition 1.6 and Theorem 1.3. -/
theorem s2v_hardt1_connected_boolean_refinement_aux {n m : ℕ}
    (c : Fin m → s2v_t11b_Formula n)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin n), ∃ i, x ∈ (c i).realize) :
    ∃ l : ℕ, ∃ d : Fin l → s2v_t11b_Formula n,
      (∀ q, IsConnected (d q).realize) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ∃ q, x ∈ (d q).realize) ∧
      Pairwise (fun q r => Disjoint (d q).realize (d r).realize) ∧
      ∀ q, ∃ i, (d q).realize ⊆ (c i).realize := by
  classical
  let R := s2v_t11b_refinementFormula c
  choose k D hU hUcover hdisj using fun s : Fin m → Bool =>
    s2v_hardt1_boolean_component_partition (R s)
  let U := fun s j => (D s j).realize
  let J := (s : Fin m → Bool) × Fin (k s)
  let E := Fintype.equivFin J
  let K : Fin (Fintype.card J) → s2v_t11b_Formula n :=
    fun q => D (E.symm q).1 (E.symm q).2
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
