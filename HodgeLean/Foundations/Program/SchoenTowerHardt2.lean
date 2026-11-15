import HodgeLean.Foundations.Program.SchoenTowerHardt2Proofs

/-! Implication from Boolean polynomial descriptions to quantified coordinate descriptions and metric approximation sets.
Graph image transport is a later slice.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- One existential spatial coordinate has a Boolean parameter description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1. -/
theorem s2v_hardt2_projection {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ d : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ d.realize ↔ ∃ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize :=
  s2v_hardt2_projection_aux f

example {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ d : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ d.realize ↔ ∃ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize :=
  s2v_hardt2_projection f

/-- One universally quantified spatial coordinate has a Boolean parameter description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, complement consequence. -/
theorem s2v_hardt2_universal {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ d : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ d.realize ↔ ∀ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize :=
  s2v_hardt2_universal_aux f

example {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ d : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ d.realize ↔ ∀ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize :=
  s2v_hardt2_universal f

/-- The metric approximation condition has an exact Boolean description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, closure consequence. -/
theorem s2v_hardt2_closure_formula {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ d : s2v_t11b_Formula n, d.realize = closure f.realize ∧
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ d.realize ↔
        ∀ ε : ℝ, 0 < ε → ∃ y ∈ f.realize,
          (∑ i : Fin n, (x i - y i)^2) < ε^2 :=
  s2v_hardt2_closure_formula_aux f

example {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ d : s2v_t11b_Formula n, d.realize = closure f.realize ∧
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ d.realize ↔
        ∀ ε : ℝ, 0 < ε → ∃ y ∈ f.realize,
          (∑ i : Fin n, (x i - y i)^2) < ε^2 :=
  s2v_hardt2_closure_formula f

example {n : ℕ} (f : s2v_t11b_Formula (n + 1)) :
    ∃ d : s2v_t11b_Formula n,
      (∀ a : EuclideanSpace ℝ (Fin n), a ∈ d.realize ↔ ∃ x : ℝ,
        WithLp.toLp 2 (Fin.cons x (fun i => a i)) ∈ f.realize) ∧
      ∀ a : d.realize, ∃ c : s2v_t11b_Formula n,
        c.realize = Subtype.val '' connectedComponent a := by
  obtain ⟨d, hd⟩ := s2v_hardt2_projection f
  exact ⟨d, hd, fun a => s2v_hardt1_component_formula d a⟩

end HodgeLean.Foundations.Program
