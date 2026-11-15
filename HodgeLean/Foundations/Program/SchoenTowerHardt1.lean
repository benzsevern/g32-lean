import HodgeLean.Foundations.Program.SchoenTowerHardt1Proofs

/-! Implication from Boolean component descriptions to usable connected Boolean parameter pieces.
This spec concerns arbitrary polynomial Boolean subsets of real Euclidean spaces.
It supplies no frontier-compatible family coordinates or general map trivialization.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- Each actual component has an exact Boolean polynomial realization in the original ambient space.
Source: Coste, Real Algebraic Sets (2005), Proposition 1.6, semialgebraicity assertion. -/
theorem s2v_hardt1_component_formula {n : ℕ} (f : s2v_t11b_Formula n)
    (x : f.realize) :
    ∃ c : s2v_t11b_Formula n,
      c.realize = Subtype.val '' connectedComponent x :=
  s2v_hardt1_component_formula_aux f x

example {n : ℕ} (f : s2v_t11b_Formula n) (x : f.realize) :
    ∃ c : s2v_t11b_Formula n,
      c.realize = Subtype.val '' connectedComponent x :=
  s2v_hardt1_component_formula f x

/-- Every finite Boolean cover has a finite disjoint connected Boolean refinement.
Source: Coste, Real Algebraic Sets (2005), Proposition 1.6 and Theorem 1.3. -/
theorem s2v_hardt1_connected_boolean_refinement {n m : ℕ}
    (c : Fin m → s2v_t11b_Formula n)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin n), ∃ i, x ∈ (c i).realize) :
    ∃ l : ℕ, ∃ d : Fin l → s2v_t11b_Formula n,
      (∀ q, IsConnected (d q).realize) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ∃ q, x ∈ (d q).realize) ∧
      Pairwise (fun q r => Disjoint (d q).realize (d r).realize) ∧
      ∀ q, ∃ i, (d q).realize ⊆ (c i).realize :=
  s2v_hardt1_connected_boolean_refinement_aux c hcover

example {n m : ℕ} (c : Fin m → s2v_t11b_Formula n)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin n), ∃ i, x ∈ (c i).realize) :
    ∃ l : ℕ, ∃ d : Fin l → s2v_t11b_Formula n,
      (∀ q, IsConnected (d q).realize) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ∃ q, x ∈ (d q).realize) ∧
      Pairwise (fun q r => Disjoint (d q).realize (d r).realize) ∧
      ∀ q, ∃ i, (d q).realize ⊆ (c i).realize :=
  s2v_hardt1_connected_boolean_refinement c hcover

end HodgeLean.Foundations.Program
