import HodgeLean.Foundations.Program.SchoenCycleCollisionCoefficientJets
import HodgeLean.Foundations.Program.SchoenCyclePowerPointStabilizer

/-! # Quotient stalk representatives of actual collision coefficients -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
open scoped Classical
namespace HodgeLean.Foundations.Program

/-- Every finite jet of an elementary collision coefficient comes from the
actual quotient stalk, with its actual stabilizer chosen intrinsically.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_retained_collision_coefficient_stalk_jet
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z) (N j : ℕ) :
    let S := Finset.univ.filter (fun i : Fin n => Point.map (g3_proj Z n i) x = a)
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ c : B.left.presheaf.stalk (γ.left x.underlying),
      γ.left.stalkMap x.underlying c - aeval (s2e_curvePowerParameter Z n x)
        (rename (fun i : S => (i : Fin n)) (esymm S ℂ j)) ∈
        IsLocalRing.maximalIdeal R ^ N := by
  obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show γ.left x.underlying ∈ (⊤ : B.left.Opens) from trivial)
  have hx : ⊤ ≤ x.left ⁻¹ᵁ (γ.left ⁻¹ᵁ U) := by
    intro z _
    change γ.left (x.left z) ∈ U
    have hz : z = IsLocalRing.closedPoint ℂ :=
      Subsingleton.elim (α := Spec ↧ℂ) _ _
    subst z
    exact hpU
  obtain ⟨c, hc⟩ := s2e_retained_collision_coefficient_jet_descent Z B n γ hγ hquot U hU
    (s2e_powerPointStabilizer Z n x) x hx (fun _ => Iff.rfl) a N j
  refine ⟨B.left.presheaf.germ U (γ.left x.underlying) hpU c, ?_⟩
  rw [γ.left.germ_stalkMap_apply]
  exact hc

end HodgeLean.Foundations.Program
