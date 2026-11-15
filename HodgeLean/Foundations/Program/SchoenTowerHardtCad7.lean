import HodgeLean.Foundations.Program.SchoenTowerHardtCad7Proofs

/-! Implication from compatible frontier cells to compact pair stages and scalar graphs.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Compatible frontier cells give compact dimension stages of the actual pair.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.5 and Theorem 1.1. -/
theorem s2v_hardt_cad7_pair {n m : ℕ}
    (f d : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (hd : IsCompact d.realize) (hdf : d.realize ⊆ f.realize)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ k : ℕ, ∃ c : Fin k → s2v_t11b_Formula n, ∃ dim : Fin k → ℕ,
      (∀ i, dim i ≤ n) ∧
      (∀ i, (c i).realize.Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = f.realize ∧
      (∀ i, Nonempty ((c i).realize ≃ₜ
        {t : EuclideanSpace ℝ (Fin (dim i)) | ∀ a, -1 < t a ∧ t a < 1})) ∧
      (∀ i, (c i).realize ⊆ d.realize ∨ Disjoint (c i).realize d.realize) ∧
      (∀ i j, (c i).realize ⊆ (b j).realize ∨
        Disjoint (c i).realize (b j).realize) ∧
      (∀ i j, ((c j).realize ∩ closure (c i).realize).Nonempty →
        (c j).realize ⊆ closure (c i).realize ∧ (j = i ∨ dim j < dim i)) ∧
      ∃ stage : Fin (n + 2) → s2v_t11b_Formula n,
        (∀ r, (stage r).realize = d.realize ∪
          ⋃ i ∈ {i | Disjoint (c i).realize d.realize ∧ dim i < r.val},
            (c i).realize) ∧
        (∀ r, IsCompact (stage r).realize) ∧
        (stage 0).realize = d.realize ∧
        (stage (Fin.last (n + 1))).realize = f.realize :=
  s2v_hardt_cad7_pair_aux f d hf hd hdf b

example {n m : ℕ} (f d : s2v_t11b_Formula n)
    (hf : IsCompact f.realize) (hd : IsCompact d.realize)
    (hdf : d.realize ⊆ f.realize) (b : Fin m → s2v_t11b_Formula n) :
    ∃ k : ℕ, ∃ c : Fin k → s2v_t11b_Formula n,
      (∀ i, (c i).realize.Nonempty) ∧ (⋃ i, (c i).realize) = f.realize := by
  obtain ⟨k, c, _, _, hne, _, hc, _⟩ := s2v_hardt_cad7_pair f d hf hd hdf b
  exact ⟨k, c, hne, hc⟩

/-- Scalar pair stages carry the actual last-coordinate graphs and overlap equations.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.5 and Theorem 1.1. -/
theorem s2v_hardt_cad7_scalar {n m : ℕ}
    (f d : s2v_t11b_Formula (n + 1)) (hf : IsCompact f.realize)
    (hd : IsCompact d.realize) (hdf : d.realize ⊆ f.realize)
    (b : Fin m → s2v_t11b_Formula (n + 1)) :
    ∃ k : ℕ, ∃ c : Fin k → s2v_t11b_Formula (n + 1), ∃ dim : Fin k → ℕ,
      (∀ i, dim i ≤ n + 1) ∧
      (∀ i, (c i).realize.Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = f.realize ∧
      (∀ i, Nonempty ((c i).realize ≃ₜ
        {t : EuclideanSpace ℝ (Fin (dim i)) | ∀ a, -1 < t a ∧ t a < 1})) ∧
      (∀ i, (c i).realize ⊆ d.realize ∨ Disjoint (c i).realize d.realize) ∧
      (∀ i j, (c i).realize ⊆ (b j).realize ∨
        Disjoint (c i).realize (b j).realize) ∧
      (∀ i j, ((c j).realize ∩ closure (c i).realize).Nonempty →
        (c j).realize ⊆ closure (c i).realize ∧ (j = i ∨ dim j < dim i)) ∧
      ∃ stage : Fin ((n + 1) + 2) → s2v_t11b_Formula (n + 1),
        (∀ r, (stage r).realize = d.realize ∪
          ⋃ i ∈ {i | Disjoint (c i).realize d.realize ∧ dim i < r.val},
            (c i).realize) ∧
        (∀ r, IsCompact (stage r).realize) ∧
        (stage 0).realize = d.realize ∧
        (stage (Fin.last ((n + 1) + 1))).realize = f.realize ∧
        ∃ graph : Fin ((n + 1) + 2) → s2v_t11b_Formula ((n + 1) + 1),
          (∀ r z,
          z ∈ (graph r).realize ↔
            WithLp.toLp 2 (fun i : Fin (n + 1) => z i.castSucc) ∈ (stage r).realize ∧
            z (Fin.last (n + 1)) = z (Fin.castSucc (Fin.last n))) ∧
          (∀ r s z, z ∈ (graph r).realize →
            (z ∈ (graph s).realize ↔
              WithLp.toLp 2 (fun i : Fin (n + 1) => z i.castSucc) ∈ (stage s).realize)) :=
  s2v_hardt_cad7_scalar_aux f d hf hd hdf b

example {n m : ℕ} (f d : s2v_t11b_Formula (n + 1))
    (hf : IsCompact f.realize) (hd : IsCompact d.realize)
    (hdf : d.realize ⊆ f.realize) (b : Fin m → s2v_t11b_Formula (n + 1)) :
    ∃ k : ℕ, ∃ c : Fin k → s2v_t11b_Formula (n + 1),
      (∀ i, (c i).realize.Nonempty) ∧ (⋃ i, (c i).realize) = f.realize := by
  obtain ⟨k, c, _, _, hne, _, hc, _⟩ := s2v_hardt_cad7_scalar f d hf hd hdf b
  exact ⟨k, c, hne, hc⟩

end HodgeLean.Foundations.Program
