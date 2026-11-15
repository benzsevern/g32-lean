import HodgeLean.Foundations.Program.SchoenCycleParameterPolynomialAction
import HodgeLean.Foundations.Program.SchoenCycleQuotientStabilizerJets
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

/-! # Actual quotient sections realizing invariant parameter jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every polynomial in the actual curve-power parameters invariant under the
tuple stabilizer is represented to any finite order by an actual quotient section.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_retained_invariant_parameter_jet_descent
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (U : B.left.Opens) (hU : IsAffineOpen U) (H : Subgroup (Equiv.Perm (Fin n)))
    (x : ComplexPoint (g3_power Z n)) (hx : ⊤ ≤ x.left ⁻¹ᵁ (γ.left ⁻¹ᵁ U))
    (hH : ∀ σ, Point.map (s2_permute Z n σ) x = x ↔ σ ∈ H)
    (N : ℕ) (p : MvPolynomial (Fin n) ℂ)
    (hp : ∀ σ ∈ H, rename σ p = p) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ c : Γ(B.left, U),
      ((g3_power Z n).left.presheaf.germ (γ.left ⁻¹ᵁ U) x.underlying (hx trivial)).hom
        ((γ.left.app U).hom c) - aeval (s2e_curvePowerParameter Z n x) p ∈
          IsLocalRing.maximalIdeal R ^ N := by
  let P := g3_power Z n
  let R := P.left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : IsClosedImmersion (x.left ≫ P.hom) := by
    rw [Over.w x]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left P.hom
  have hclosed : IsClosed ({x.underlying} : Set P.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  apply s2e_quotient_invariant_stalk_jet_descent P B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n)
    γ hγ hquot U hU H x hx hclosed hH N (aeval (s2e_curvePowerParameter Z n x) p)
  intro σ hσ
  have he := s2e_fixed_permutation_parameter_polynomial Z n σ x ((hH σ).mpr hσ) p
  have hpσ : rename σ.symm p = p := hp σ⁻¹ (H.inv_mem hσ)
  rw [hpσ] at he
  rw [he, sub_self]
  exact Ideal.zero_mem _

end HodgeLean.Foundations.Program
