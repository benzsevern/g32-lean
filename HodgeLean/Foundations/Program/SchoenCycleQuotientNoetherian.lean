import HodgeLean.Foundations.Program.SchoenCycleQuotientIdealContraction
import HodgeLean.Foundations.Program.SchoenCycleIdealContractionNoetherian
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian local algebra of the retained quotient -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The finite categorical quotient of the smooth complex source is locally Noetherian.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1,
§1; Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 6, Proposition 6.1. -/
theorem s2e_quotient_isLocallyNoetherian
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v) :
    IsLocallyNoetherian Y.left := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  constructor
  intro U
  letI : IsNoetherianRing Γ(X.left, q.left ⁻¹ᵁ U.1) :=
    IsLocallyNoetherian.component_noetherian ⟨_, U.2.preimage q.left⟩
  apply s2e_isNoetherianRing_of_ideal_contraction (q.left.app U.1).hom
  intro J
  exact s2e_quotient_affine_ideal_contraction X Y G a ha1 hamul q hinv hquot U.1 U.2 J

#print axioms s2e_quotient_isLocallyNoetherian
end HodgeLean.Foundations.Program
