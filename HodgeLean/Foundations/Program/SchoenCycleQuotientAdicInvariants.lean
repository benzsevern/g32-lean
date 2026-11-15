import HodgeLean.Foundations.Program.SchoenCycleQuotientNoetherian
import HodgeLean.Foundations.Program.SchoenCycleQuotientChartAlgebra
import HodgeLean.Foundations.Program.SchoenCycleAdicEqualizer

/-! # Adic invariants of the actual quotient chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- For every ideal on an actual quotient affine chart, the adic base ring maps
bijectively to the invariant elements of the adic inverse-image chart module.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1,
§1; Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10, Proposition 10.12. -/
theorem s2e_quotient_affine_adic_fixed_points
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(Y.left, U)) :
    let R := Γ(Y.left, U)
    let A := Γ(X.left, q.left ⁻¹ᵁ U)
    letI : Algebra R A := (q.left.app U).hom.toAlgebra
    ∀ x : AdicCompletion I A,
      (∀ g, AdicCompletion.map I
        (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U).toLinearMap x = x) ↔
      ∃! y : AdicCompletion I R, AdicCompletion.map I (Algebra.linearMap R A) y = x := by
  let R := Γ(Y.left, U)
  let A := Γ(X.left, q.left ⁻¹ᵁ U)
  letI : Algebra R A := (q.left.app U).hom.toAlgebra
  letI : Fintype G := Fintype.ofFinite G
  letI : IsLocallyNoetherian Y.left :=
    s2e_quotient_isLocallyNoetherian X Y G a ha1 hamul q hinv hquot
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : Module.Finite R A := q.left.finite_app U hU
  letI := IsSchemeTheoreticallyDominant.of_isDominant q.left
  dsimp only
  intro x
  apply s2e_adic_finite_fixed_points I (Algebra.linearMap R A)
    (fun g => (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U).toLinearMap)
    (q.left.app_injective U)
  · intro g r
    exact (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U).commutes r
  · intro b hb
    obtain ⟨r, hr, _⟩ := s2e_step1_invariant_affine_descent X Y G a ha1 hamul
      q hinv hquot U hU b (fun g => hb g)
    exact ⟨r, hr⟩

#print axioms s2e_quotient_affine_adic_fixed_points
end HodgeLean.Foundations.Program
