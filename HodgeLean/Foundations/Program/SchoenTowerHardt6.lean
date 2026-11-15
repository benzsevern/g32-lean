import HodgeLean.Foundations.Program.SchoenTowerHardt6Proofs

/-! Implication from the finite-carrier construction to zero-dimensional compatible triangulation.
Only finite Boolean carriers are covered here; positive-dimensional extension is future work.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- Finite Boolean carriers have a singleton-face triangulation preserving every designated subset.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.10, finite-carrier case. -/
theorem s2v_hardt6_finite_triangulation {n m : ℕ}
    (f : s2v_t11b_Formula n) (hf : f.realize.Finite)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ K.space = f.realize ∧
      (∀ s ∈ K.faces, ∃ x ∈ f.realize, s = {x}) ∧
      ∃ h : K.space ≃ₜ f.realize,
        (∀ x, (h x).val = x.val) ∧
        (∀ y, (h.symm y).val = y.val) ∧
        (∀ j, ∃ S : Finset (EuclideanSpace ℝ (Fin n)),
          (↑S : Set (EuclideanSpace ℝ (Fin n))) ⊆ K.vertices ∧
          f.realize ∩ (b j).realize = ⋃ x ∈ S, ({x} : Set _)) ∧
        ∃ g : s2v_t11b_Formula (n + n), ∀ z,
          z ∈ g.realize ↔ ∃ x : K.space,
            (∀ i, z (Fin.castAdd n i) = x.val i) ∧
            (∀ i, z (Fin.natAdd n i) = (h x).val i) :=
  s2v_hardt6_finite_triangulation_aux f hf b

example {n : ℕ} (f : s2v_t11b_Formula n) (hf : f.realize.Finite) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ K.space = f.realize := by
  obtain ⟨K, hK, hspace, _⟩ :=
    s2v_hardt6_finite_triangulation f hf (fun i : Fin 0 => Fin.elim0 i)
  exact ⟨K, hK, hspace⟩

end HodgeLean.Foundations.Program
