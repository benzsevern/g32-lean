import HodgeLean.Foundations.Program.SchoenCycleS1j3Proofs

/-! # Mixed branch equations and analytic generators
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

/-- The actual insertion image has a local generator equal to a unit times its block constant coefficient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15. -/
theorem s2e_mixed_branch_generator
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
    (e : OpenPartialHomeomorph (ComplexPoint B) (Fin n → ℂ))
    (he : ∀ᶠ q in 𝓝 x, ∀ a (j : Fin (m a)),
      e (Point.map γ q) (ι ⟨a, j⟩) =
        (-1 : ℂ) ^ (m a - j.val) *
        aeval (fun i : Fin (m a) =>
          (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
            (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
              (Point.map (g3_proj Z n (ι ⟨a, i⟩)) q) -
             extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)))
          (esymm (Fin (m a)) ℂ (m a - j.val)))
    (q : ℕ) (hq : n = q + 1) (a : Fin b) :
    let γq : g3_power Z (q + 1) ⟶ B := eqToHom (congrArg (g3_power Z) hq.symm) ≫ γ
    ∃ (U : B.left.affineOpens) (_hU : γ.left x.underlying ∈ U.1)
      (c : Γ(B.left, U.1)) (η : (Fin n → ℂ) → ℂ),
      (s2c_branchIdeal Z B q γq (p a)).ideal U = Ideal.span {c} ∧
      AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0,
        let v := (ComplexPoint.localChart B n (Point.map γ x)).symm
          (ComplexPoint.localChart B n (Point.map γ x) (Point.map γ x) + z)
        Point.evaluate U.1 c v = η z * e v (ι ⟨a, ⟨0, hm a⟩⟩)) :=
  s2e_mixed_branch_generator_aux Z B n γ hγ hquot x b m hm ι p hp hx e he q hq a

example := @s2e_mixed_branch_generator

/-- A tuple with no marked coordinate lies in an affine open where the actual branch ideal is the unit ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15. -/
theorem s2e_branch_equation_off_support
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (p : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x ≠ p)
    (q : ℕ) (hq : n = q + 1) :
    let γq : g3_power Z (q + 1) ⟶ B := eqToHom (congrArg (g3_power Z) hq.symm) ≫ γ
    ∃ (U : B.left.affineOpens), γ.left x.underlying ∈ U.1 ∧
      (s2c_branchIdeal Z B q γq p).ideal U = ⊤ :=
  s2e_branch_equation_off_support_aux Z B n γ hγ hquot x p hx q hq

example := @s2e_branch_equation_off_support

end HodgeLean.Foundations.Program
