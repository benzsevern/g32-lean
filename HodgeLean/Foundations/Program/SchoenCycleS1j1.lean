import HodgeLean.Foundations.Program.SchoenCycleS1j1Proofs

/-! # Mixed collision coefficient neighbourhoods
Implication from the explicit inputs to the stated local comparisons.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MvPolynomial
open Filter Topology Manifold HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program

/-- The retained symmetric quotient has the dimension of its divisor length.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15. -/
theorem s2e_retained_quotient_relative_dimension
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    : SmoothOfRelativeDimension n B.hom :=
  s2e_retained_quotient_relative_dimension_aux Z B n γ hγ hquot

example := @s2e_retained_quotient_relative_dimension

/-- The exact monic coefficients of all collision blocks form an analytic neighbourhood chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15. -/
theorem s2e_mixed_coefficient_neighbourhood
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    [SmoothOfRelativeDimension n B.hom]
    (x : ComplexPoint (g3_power Z n)) (b : ℕ) (m : Fin b → ℕ)
    (hm : ∀ a, 0 < m a) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    : ∃ e : OpenPartialHomeomorph (ComplexPoint B) (Fin n → ℂ),
      Point.map γ x ∈ e.source ∧ e (Point.map γ x) = 0 ∧
      AnalyticAt ℂ (fun z => e ((ComplexPoint.localChart B n (Point.map γ x)).symm
        (ComplexPoint.localChart B n (Point.map γ x) (Point.map γ x) + z))) 0 ∧
      AnalyticAt ℂ (fun z => ComplexPoint.localChart B n (Point.map γ x) (e.symm z)) 0 ∧
      (∀ᶠ q in 𝓝 x, ∀ a (j : Fin (m a)),
        e (Point.map γ q) (ι ⟨a, j⟩) =
          (-1 : ℂ) ^ (m a - j.val) *
          aeval (fun i : Fin (m a) =>
            (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
              (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
                (Point.map (g3_proj Z n (ι ⟨a, i⟩)) q) -
               extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)))
            (esymm (Fin (m a)) ℂ (m a - j.val))) :=
  s2e_mixed_coefficient_neighbourhood_aux Z B n γ hγ hquot x b m hm ι p hp hx

example := @s2e_mixed_coefficient_neighbourhood

/-- Every prescribed high-order block coefficient jet can be represented by actual étale algebraic coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15. -/
theorem s2e_mixed_algebraic_coefficient_neighbourhood
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    [SmoothOfRelativeDimension n B.hom]
    (x : ComplexPoint (g3_power Z n)) (b : ℕ) (m : Fin b → ℕ)
    (hm : ∀ a, 0 < m a) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (N : ℕ) (hN : n < N) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ D : LocalEtaleCoordinates B n (γ.left x.underlying),
      ∀ a (j : Fin (m a)),
        γ.left.stalkMap x.underlying
          (B.left.presheaf.germ D.neighborhood (γ.left x.underlying) D.mem
            (D.coordinateAlgHom (X (ι ⟨a, j⟩)))) -
        aeval (s2e_curvePowerParameter Z n x)
          (rename (fun i : Fin (m a) => ι ⟨a, i⟩)
            (esymm (Fin (m a)) ℂ (j.val + 1))) ∈
          IsLocalRing.maximalIdeal R ^ N :=
  s2e_mixed_algebraic_coefficient_neighbourhood_aux Z B n γ hγ hquot x b m hm ι p hp hx N hN

example := @s2e_mixed_algebraic_coefficient_neighbourhood

end HodgeLean.Foundations.Program
