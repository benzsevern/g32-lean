import HodgeLean.Foundations.Program.SchoenCycleMixedQuotientFormalValues
import HodgeLean.Foundations.Program.SchoenCycleFormalCoordinateRepresentatives
import HodgeLean.Foundations.Program.SchoenCycleFormalPullbackJetError
import HodgeLean.Foundations.Program.SchoenCycleQuotientFiniteType
import HodgeLean.Foundations.Program.SchoenCycleMixedPolynomialGenerators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Actual mixed elementary coefficient jets have simultaneous algebraic stalk representatives whose classes form a cotangent basis of the retained quotient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_mixed_coefficient_cotangent_representatives
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (b : ℕ) (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a) (N : ℕ) :
    let S := B.left.presheaf.stalk (γ.left x.underlying)
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (γ.left x.underlying)).toAlgebra
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ (c : (Σ a, Fin (m a)) → S) (hc : ∀ v, c v ∈ IsLocalRing.maximalIdeal S)
      (D : Module.Basis (Σ a, Fin (m a)) ℂ (IsLocalRing.maximalIdeal S).Cotangent),
      (∀ v, D v = (IsLocalRing.maximalIdeal S).toCotangent ⟨c v, hc v⟩) ∧
      ∀ a (j : Fin (m a)), γ.left.stalkMap x.underlying (c ⟨a, j⟩) -
        aeval (s2e_curvePowerParameter Z n x)
          (rename (fun i : Fin (m a) => ι ⟨a, i⟩)
            (esymm (Fin (m a)) ℂ (j.val + 1))) ∈ IsLocalRing.maximalIdeal R ^ N := by
  dsimp only
  let S := B.left.presheaf.stalk (γ.left x.underlying)
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (γ.left x.underlying)).toAlgebra
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : LocallyOfFiniteType B.hom := s2e_finite_surjective_locallyOfFiniteType (g3_power Z n) B γ
  letI : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  obtain ⟨F, hF⟩ := s2e_mixed_quotient_formal_values_at_point Z B n γ hγ hquot x b m ι p hp hx
  obtain ⟨c, hc, D, hD, herr⟩ := s2e_formal_coordinate_representatives F (N + 2) (by omega)
  refine ⟨c, hc, D, hD, ?_⟩
  intro a j
  let z := F.symm (AdicCompletion.of (idealOfVars (Σ a, Fin (m a)) ℂ)
    (MvPolynomial (Σ a, Fin (m a)) ℂ) (X ⟨a, j⟩))
  let v := aeval (s2e_curvePowerParameter Z n x)
    (rename (fun i : Fin (m a) => ι ⟨a, i⟩) (esymm (Fin (m a)) ℂ (j.val + 1)))
  have hz : s2e_formal_stalk_pullback (g3_power Z n) B γ x.underlying z =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) R v := by
    have hh := hF (X ⟨a, j⟩)
    rw [s2e_mixed_polynomial_invariant_X, rename_rename] at hh
    exact hh
  have he : (AdicCompletion.of (IsLocalRing.maximalIdeal S) S (c ⟨a, j⟩) - z).val N = 0 := by
    apply (s2e_adic_extended_power_mem_iff (IsLocalRing.maximalIdeal S)
      (IsNoetherian.noetherian _) N _).mp
    rw [← AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.pow_le_pow_right (Nat.le_add_right N 2) (herr ⟨a, j⟩)
  exact s2e_formal_pullback_jet_error (IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal R)
    (s2e_complex_stalk_pullback (g3_power Z n) B γ x.underlying)
    (s2e_complex_stalk_pullback_preserves_powers (g3_power Z n) B γ x.underlying)
    N (c ⟨a, j⟩) z v hz he

#print axioms s2e_mixed_coefficient_cotangent_representatives
end HodgeLean.Foundations.Program
