import HodgeLean.Foundations.Program.SchoenCycleMixedElementaryNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleScaledSignedBlockCoefficientEquiv
import HodgeLean.Foundations.Program.SchoenCycleLineEquivNormalization
import HodgeLean.Foundations.Program.SchoenCycleElementaryScaling
import HodgeLean.Foundations.Program.SchoenCycleRetainedQuotientSmoothNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleComplexNeighbourhoodDimension
import HodgeLean.Foundations.Program.SchoenCycleCotangentEtaleCoordinates
import HodgeLean.Foundations.Program.SchoenCycleMixedCoefficientCotangentRepresentatives
import HodgeLean.Foundations.Program.SchoenCycleS1i1
import HodgeLean.Foundations.Program.SchoenCyclePreparedResidues

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
theorem s2e_retained_quotient_relative_dimension_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    : SmoothOfRelativeDimension n B.hom := by
  exact s2e_relativeDimension_of_complex_lift_neighbourhoods (g3_power Z n) B γ n
    (s2e_retained_quotient_standardSmooth_neighbourhood Z B n γ hγ hquot)

/-- The exact monic coefficients of all collision blocks form an analytic neighbourhood chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15. -/
theorem s2e_mixed_coefficient_neighbourhood_aux
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
            (esymm (Fin (m a)) ℂ (m a - j.val))) := by
  obtain ⟨e₀, he₀, hz₀, hf₀, hi₀, hv₀⟩ :=
    s2e_mixed_elementary_analytic_neighbourhood Z B n γ hγ hquot x b m ι p hp hx
  let L := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
  obtain ⟨hL, hLv⟩ := s2e_line_equiv_native_normalization L
  let c : ℂ := ((L 1) 0)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hL
  obtain ⟨A, hA⟩ := s2e_scaled_signed_block_coefficient_equiv n b m ι c hc
  let e := e₀.trans A.toHomeomorph.toOpenPartialHomeomorph
  have he : Point.map γ x ∈ e.source := ⟨he₀, trivial⟩
  have hz : e (Point.map γ x) = 0 := by
    change A (e₀ (Point.map γ x)) = 0
    rw [hz₀, map_zero]
  refine ⟨e, he, hz, ?_, ?_, ?_⟩
  · exact (A.toContinuousLinearMap.analyticAt _).comp hf₀
  · exact hi₀.comp_of_eq (A.symm.toContinuousLinearMap.analyticAt 0) (map_zero A.symm)
  · filter_upwards [hv₀] with q hq
    intro a j
    have hk : j.rev.val + 1 = m a - j.val := by
      rw [Fin.val_rev]
      omega
    have hroot (i : Fin (m a)) :
        L.symm (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
            (Point.map (g3_proj Z n (ι ⟨a, i⟩)) q) -
          extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)) =
        c * (ComplexPoint.localChart Z 1 (p a)
          (Point.map (g3_proj Z n (ι ⟨a, i⟩)) q) 0 -
            ComplexPoint.localChart Z 1 (p a) (p a) 0) := by
      rw [hLv]
      rfl
    change A (e₀ (Point.map γ q)) (ι ⟨a, j⟩) = _
    rw [hA, hq a j.rev, hk]
    rw [mul_assoc]
    rw [← s2e_elementary_evaluation_scale]
    apply congrArg (fun r : Fin (m a) → ℂ =>
      (-1 : ℂ) ^ (m a - j.val) * aeval r (esymm (Fin (m a)) ℂ (m a - j.val)))
    funext i
    exact (hroot i).symm

/-- Every prescribed high-order block coefficient jet can be represented by actual étale algebraic coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15. -/
theorem s2e_mixed_algebraic_coefficient_neighbourhood_aux
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
          IsLocalRing.maximalIdeal R ^ N := by
  dsimp only
  letI : Algebra ℂ (B.left.presheaf.stalk (γ.left x.underlying)) :=
    (HodgeLean.Foundations.Curves.stalkC (γ.left x.underlying)).toAlgebra
  obtain ⟨c, hc, D, hD, herr⟩ :=
    s2e_mixed_coefficient_cotangent_representatives Z B n γ hγ hquot x b m ι p hp hx N
  have hbFin (i : Fin n) : (D.reindex ι) i =
      (IsLocalRing.maximalIdeal (B.left.presheaf.stalk (γ.left x.underlying))).toCotangent
        ⟨c (ι.symm i), hc (ι.symm i)⟩ := by
    rw [Module.Basis.reindex_apply]
    exact hD (ι.symm i)
  obtain ⟨E, hE⟩ := s2e_localEtaleCoordinates_of_cotangent_basis B n (Point.map γ x)
    (c ∘ ι.symm) (fun i => hc (ι.symm i)) (D.reindex ι) hbFin
  refine ⟨E, ?_⟩
  intro a j
  erw [hE, Function.comp_apply, Equiv.symm_apply_apply]
  exact herr a j

end HodgeLean.Foundations.Program
