import HodgeLean.Foundations.Program.SchoenTowerHardt3Proofs

/-! Implication from Boolean polynomial descriptions to finite connected parameter pieces and continuous Boolean root sections.
Bands and inductive adapted cylindrical decompositions are later slices.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- A finite polynomial family has connected Boolean pieces with Boolean ordered root sections.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical construction on pp. 6–7. -/
theorem s2v_hardt3_root_sections {n k : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, IsConnected (c i).realize) ∧
      (∀ a : EuclideanSpace ℝ (Fin n), ∃ i, a ∈ (c i).realize) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      ∀ i, ∃ r : ℕ, ∃ ψ : Fin r → (c i).realize → ℝ,
        (∀ v, Continuous (ψ v)) ∧
        (∀ a, StrictMono (fun v => ψ v a)) ∧
        (∀ j, (∀ a : (c i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
          (∀ a : (c i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
        (∀ a : (c i).realize, ∀ x : ℝ,
          (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
            (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) x = 0) ↔
            ∃ v, x = ψ v a) ∧
        ∀ v, ∃ g : s2v_t11b_Formula (n + 1),
          ∀ a : EuclideanSpace ℝ (Fin n), ∀ x : ℝ,
            WithLp.toLp 2 (Fin.cons x (fun j => a j)) ∈ g.realize ↔
              ∃ ha : a ∈ (c i).realize, x = ψ v ⟨a, ha⟩ :=
  s2v_hardt3_root_sections_aux P

example {n k : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, IsConnected (c i).realize) ∧
      (∀ a : EuclideanSpace ℝ (Fin n), ∃ i, a ∈ (c i).realize) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      ∀ i, ∃ r : ℕ, ∃ ψ : Fin r → (c i).realize → ℝ,
        (∀ v, Continuous (ψ v)) ∧
        (∀ a, StrictMono (fun v => ψ v a)) ∧
        (∀ j, (∀ a : (c i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
          (∀ a : (c i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
        (∀ a : (c i).realize, ∀ x : ℝ,
          (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
            (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) x = 0) ↔
            ∃ v, x = ψ v a) ∧
        ∀ v, ∃ g : s2v_t11b_Formula (n + 1),
          ∀ a : EuclideanSpace ℝ (Fin n), ∀ x : ℝ,
            WithLp.toLp 2 (Fin.cons x (fun j => a j)) ∈ g.realize ↔
              ∃ ha : a ∈ (c i).realize, x = ψ v ⟨a, ha⟩ :=
  s2v_hardt3_root_sections P

end HodgeLean.Foundations.Program
