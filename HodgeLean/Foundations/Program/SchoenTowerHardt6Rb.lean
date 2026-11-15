import HodgeLean.Foundations.Program.SchoenTowerHardt6RbProofs
import HodgeLean.Foundations.Program.SchoenTowerHardt6

/-! Implication from fresh compact triangulation to compatible relative open faces.
The parametrization is chosen afresh; scalar interpolation is a later unit.
HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- Compact Boolean carriers have fresh compatible triangulations with actual map graphs.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.10, printed p. 9;
Theorem 1.1 for coordinate interchange. -/
theorem s2v_hardt6rb_compatible_triangulation {n m : ℕ}
    (f : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ ∃ h : K.space ≃ₜ f.realize,
        (∀ j, ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin n))),
          (↑S : Set _) ⊆ K.faces ∧
          f.realize ∩ (b j).realize =
            (fun x : K.space => (h x).val) ''
              {x : K.space | ∃ s ∈ S,
                x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ g : s2v_t11b_Formula (n + n),
          (∀ z, z ∈ g.realize ↔ ∃ x : K.space,
            (∀ i, z (Fin.castAdd n i) = x.val i) ∧
            (∀ i, z (Fin.natAdd n i) = (h x).val i)) ∧
          (∀ z : EuclideanSpace ℝ (Fin (n + n)),
            WithLp.toLp 2 (fun i =>
              Fin.addCases (fun j => z (Fin.natAdd n j))
                (fun j => z (Fin.castAdd n j)) i) ∈ g.realize ↔
              ∃ y : f.realize,
                (∀ i, z (Fin.castAdd n i) = y.val i) ∧
                (∀ i, z (Fin.natAdd n i) = (h.symm y).val i)) :=
  s2v_hardt6rb_compatible_triangulation_aux f hf b

example {n m : ℕ} (f : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ Nonempty (K.space ≃ₜ f.realize) := by
  obtain ⟨K, hK, h, _⟩ := s2v_hardt6rb_compatible_triangulation f hf b
  exact ⟨K, hK, ⟨h⟩⟩

example {n m : ℕ} (f d : s2v_t11b_Formula n)
    (hf : IsCompact f.realize) (hd : IsCompact d.realize)
    (hdf : d.realize ⊆ f.realize) (b : Fin m → s2v_t11b_Formula n) :
    ∃ k : ℕ, ∃ c : Fin k → s2v_t11b_Formula n,
      (∀ i, (c i).realize.Nonempty) ∧ (⋃ i, (c i).realize) = f.realize := by
  obtain ⟨k, c, _, _, hne, _, hc, _⟩ := s2v_hardt_cad7_pair f d hf hd hdf b
  exact ⟨k, c, hne, hc⟩

example {n m : ℕ} (f : s2v_t11b_Formula n) (hf : f.realize.Finite)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ K.space = f.realize := by
  obtain ⟨K, hK, hspace, _⟩ := s2v_hardt6_finite_triangulation f hf b
  exact ⟨K, hK, hspace⟩

end HodgeLean.Foundations.Program
