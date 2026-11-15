import HodgeLean.Foundations.Program.SchoenTowerHardtCad1Proofs

/-! Implication from finite real cuts to Boolean point and interval cell geometry.
The scope is one variable, including both unbounded intervals and the empty cut family.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finite cuts give nonempty Boolean cells with box charts and strict frontier incidence.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3 and the one-variable
CAD construction, printed pp. 6–7; frontier discussion on printed p. 7. -/
theorem s2v_hardt_cad1_cut_cells (R : Finset ℝ) :
    ∃ c : Fin (2 * R.card + 1) → s2v_t11b_Formula 1,
    ∃ dim : Fin (2 * R.card + 1) → ℕ,
      (∀ i, (c i).realize.Nonempty) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i, dim i ≤ 1) ∧
      (∀ i, Nonempty ((c i).realize ≃ₜ
        {t : EuclideanSpace ℝ (Fin (dim i)) | ∀ a, -1 < t a ∧ t a < 1})) ∧
      (∀ i, (dim i = 0 ↔ ∃ r ∈ R,
        (c i).realize = {x : EuclideanSpace ℝ (Fin 1) | x 0 = r})) ∧
      (∀ i, dim i = 1 → IsOpen (c i).realize ∧
        Set.OrdConnected {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈ (c i).realize} ∧
        ∀ x ∈ (c i).realize, x 0 ∉ R) ∧
      (∀ i (x y : EuclideanSpace ℝ (Fin 1)), x ∈ (c i).realize →
        y ∈ (c i).realize → ∀ r ∈ R,
          (x 0 ≤ r ↔ y 0 ≤ r) ∧ (r ≤ x 0 ↔ r ≤ y 0)) ∧
      (∀ i j, ((c j).realize ∩ closure (c i).realize).Nonempty →
        (c j).realize ⊆ closure (c i).realize ∧ (j = i ∨ dim j < dim i)) :=
  s2v_hardt_cad1_cut_cells_aux R

example (R : Finset ℝ) : ∃ c : Fin (2 * R.card + 1) → s2v_t11b_Formula 1,
    (⋃ i, (c i).realize) = Set.univ := by
  obtain ⟨c, _, _, _, hc, _⟩ := s2v_hardt_cad1_cut_cells R
  exact ⟨c, hc⟩

end HodgeLean.Foundations.Program
