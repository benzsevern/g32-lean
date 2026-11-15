import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactMarkedRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFiniteCellMarkSelection

/-! A common actual cell triangulation yields compatible triangulations of each compact Boolean marked carrier. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_carrier_from_cells {n m : ℕ} {ι : Type*} [Fintype ι]
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hK : K.faces.Finite)
    (A : Set (EuclideanSpace ℝ (Fin n))) (H : K.space ≃ₜ A)
    (c : ι → Set (EuclideanSpace ℝ (Fin n))) (hcover : (⋃ i, c i) = A)
    (hcell : ∀ i, ∃ R : Finset (Finset (EuclideanSpace ℝ (Fin n))),
      (↑R : Set _) ⊆ K.faces ∧ c i = (fun x : K.space => (H x).val) ''
        {x : K.space | ∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))})
    (f : s2v_t11b_Formula n) (hf : IsCompact f.realize) (hfA : f.realize ⊆ A)
    (b : Fin m → s2v_t11b_Formula n)
    (hcf : ∀ i, c i ⊆ f.realize ∨ Disjoint (c i) f.realize)
    (hcb : ∀ i j, c i ⊆ (b j).realize ∨ Disjoint (c i) (b j).realize)
    (G : s2v_t11b_Formula (n + n))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : K.space,
      (∀ i, z (Fin.castAdd n i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (H x).val i)) :
    ∃ D : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)), D.faces.Finite ∧
      ∃ h : D.space ≃ₜ f.realize,
        (∀ j, ∃ R : Finset (Finset (EuclideanSpace ℝ (Fin n))),
          (↑R : Set _) ⊆ D.faces ∧ f.realize ∩ (b j).realize = (fun x : D.space => (h x).val) ''
            {x : D.space | ∃ s ∈ R, x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ J : s2v_t11b_Formula (n + n), ∀ z, z ∈ J.realize ↔ ∃ x : D.space,
          (∀ i, z (Fin.castAdd n i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (h x).val i) := by
  obtain ⟨S, hS, hSM⟩ := s2v_hardt6rb_finite_cell_mark_selection A f.realize c hcover hcf K H hcell
  exact s2v_hardt6rb_compact_marked_restriction K hK A f.realize hf hfA (fun j => (b j).realize) H S hS hSM
    (fun j => s2v_hardt6rb_finite_cell_mark_selection A (b j).realize c hcover (fun i => hcb i j) K H hcell) G hG

end HodgeLean.Foundations.Program
