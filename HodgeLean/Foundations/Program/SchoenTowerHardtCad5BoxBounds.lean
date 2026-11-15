import HodgeLean.Foundations.Program.SchoenTowerHardtCad5CoordinateFibers
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5AlgebraicRank
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-! Dimension bounds for finite Boolean relations covering a real box. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_box_finite_relations_bound {d k : ℕ}
    (m : Fin k → ℕ) (Y : (j : Fin k) → Set (EuclideanSpace ℝ (Fin (m j))))
    (G : (j : Fin k) → s2v_t11b_Formula (m j + d))
    (hfin : ∀ j y, y ∈ Y j → {x : EuclideanSpace ℝ (Fin d) |
      WithLp.toLp 2 (Fin.append (fun i => y i) (fun i => x i)) ∈ (G j).realize}.Finite)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin d), (∀ i, -1 < x i ∧ x i < 1) →
      ∃ j, ∃ y ∈ Y j, WithLp.toLp 2
        (Fin.append (fun i => y i) (fun i => x i)) ∈ (G j).realize) :
    ∃ j, d ≤ m j := by
  classical
  choose K hK hAlg using fun j => s2v_hardt_cad5_finite_graph_fiber_algebraic (G j)
  let s : Set ℝ := ⋃ j, (K j : Set ℝ)
  have hs : s.Countable := Set.countable_iUnion (fun j => by
    letI := hK j
    exact Set.to_countable _)
  let K₀ : Subfield ℝ := Subfield.closure s
  letI : Countable K₀ := s2v_hardt_cad5_countable_coefficient_field s hs
  have hKK (j : Fin k) : K j ≤ K₀ := by
    intro c hc
    exact Subfield.subset_closure (Set.mem_iUnion.mpr ⟨j, hc⟩)
  obtain ⟨x, hx, hbox⟩ := s2v_hardt_cad5_independent_box_point K₀ d
  obtain ⟨j, y, hy, hrel⟩ := hcover x hbox
  let L := (IntermediateField.adjoin K₀ (Set.range (fun i => y i))).toSubfield
  have hKL : K₀ ≤ L := by
    intro c hc
    exact (IntermediateField.adjoin K₀ (Set.range (fun i => y i))).algebraMap_mem ⟨c, hc⟩
  let a : Fin (m j) → L := fun i => ⟨y i, IntermediateField.subset_adjoin K₀ _ ⟨i, rfl⟩⟩
  have halg : ∀ i, IsAlgebraic L (x i) :=
    hAlg j L ((hKK j).trans hKL) a (hfin j y hy) x hrel
  refine ⟨j, s2v_hardt_cad5_independent_le_coordinates K₀
    (fun i => x i) (fun i => y i) hx ?_⟩
  intro i
  exact IntermediateField.isAlgebraic_adjoin_iff.mp (halg i)

theorem s2v_hardt_cad5_open_finite_relations_bound {d k : ℕ}
    (m : Fin k → ℕ) (Y : (j : Fin k) → Set (EuclideanSpace ℝ (Fin (m j))))
    (G : (j : Fin k) → s2v_t11b_Formula (m j + d))
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : ∀ j y, y ∈ Y j → {x : EuclideanSpace ℝ (Fin d) |
      WithLp.toLp 2 (Fin.append (fun i => y i) (fun i => x i)) ∈ (G j).realize}.Finite)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin d), x ∈ U →
      ∃ j, ∃ y ∈ Y j, WithLp.toLp 2
        (Fin.append (fun i => y i) (fun i => x i)) ∈ (G j).realize) :
    ∃ j, d ≤ m j := by
  classical
  choose K hK hAlg using fun j => s2v_hardt_cad5_finite_graph_fiber_algebraic (G j)
  let s : Set ℝ := ⋃ j, (K j : Set ℝ)
  have hs : s.Countable := Set.countable_iUnion (fun j => by
    letI := hK j
    exact Set.to_countable _)
  let K₀ : Subfield ℝ := Subfield.closure s
  letI : Countable K₀ := s2v_hardt_cad5_countable_coefficient_field s hs
  have hKK (j : Fin k) : K j ≤ K₀ := by
    intro c hc
    exact Subfield.subset_closure (Set.mem_iUnion.mpr ⟨j, hc⟩)
  obtain ⟨x, hxU, hx⟩ := s2v_hardt_cad5_independent_open_point K₀ U hU hne
  obtain ⟨j, y, hy, hrel⟩ := hcover x hxU
  let L := (IntermediateField.adjoin K₀ (Set.range (fun i => y i))).toSubfield
  have hKL : K₀ ≤ L := by
    intro c hc
    exact (IntermediateField.adjoin K₀ (Set.range (fun i => y i))).algebraMap_mem ⟨c, hc⟩
  let a : Fin (m j) → L := fun i => ⟨y i, IntermediateField.subset_adjoin K₀ _ ⟨i, rfl⟩⟩
  have halg : ∀ i, IsAlgebraic L (x i) :=
    hAlg j L ((hKK j).trans hKL) a (hfin j y hy) x hrel
  refine ⟨j, s2v_hardt_cad5_independent_le_coordinates K₀
    (fun i => x i) (fun i => y i) hx ?_⟩
  intro i
  exact IntermediateField.isAlgebraic_adjoin_iff.mp (halg i)

end HodgeLean.Foundations.Program
