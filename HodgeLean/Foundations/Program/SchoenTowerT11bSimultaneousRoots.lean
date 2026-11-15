import HodgeLean.Foundations.Program.SchoenTowerT11bActiveAtoms

/-! Common finite Boolean refinements for simultaneous polynomial root enumeration.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite polynomial family has a common finite Boolean cover on which every polynomial has continuous ordered roots over connected subsets of the nonzero-fiber region.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, simultaneous root refinement step. -/
theorem s2v_t11b_simultaneous_finite_root_pieces {ι : Type*} [Fintype ι] {n : ℕ}
    (P : ι → Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ t : EuclideanSpace ℝ (Fin n), (∀ j, (P j).map (MvPolynomial.eval (fun v => t v)) ≠ 0) →
        ∃ i, t ∈ (c i).realize) ∧
      ∀ i (K : Set (EuclideanSpace ℝ (Fin n))), K ⊆ (c i).realize → IsPreconnected K → ∀ a : K,
        ∀ j, ∃ r : ℕ, ∃ ψ : Fin r → K → ℝ,
          (∀ v, Continuous (ψ v)) ∧ (∀ t, StrictMono (fun v => ψ v t)) ∧
          ∀ t : K, ∀ x : ℝ, (P j).eval₂ (MvPolynomial.eval (fun v => t.val v)) x = 0 ↔
            ∃ v, x = ψ v t := by
  classical
  choose m c hcover hroots using (fun j => s2v_t11b_finite_pieces_ordered_roots (P j))
  let J := (j : ι) → Fin (m j)
  let C : J → s2v_t11b_Formula n := fun f => s2v_t11b_Formula.conjunction
    (Finset.univ.toList.map (fun j => c j (f j)))
  have hC : ∀ f t, t ∈ (C f).realize ↔ ∀ j, t ∈ (c j (f j)).realize := by
    intro f t
    simp only [C, s2v_t11b_realize_conjunction, List.forall_mem_map,
      Finset.mem_toList, Finset.mem_univ, forall_true_left]
  let E := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun i => C (E i), ?_, ?_⟩
  · intro t ht
    choose f hf using (fun j => hcover j t (ht j))
    refine ⟨E.symm f, ?_⟩
    change t ∈ (C (E (E.symm f))).realize
    rw [E.apply_symm_apply]
    exact (hC f t).mpr hf
  · intro i K hsub hK a j
    exact hroots j (E i j) K (fun t ht => (hC (E i) t).mp (hsub ht) j) hK a

end HodgeLean.Foundations.Program
