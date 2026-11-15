import HodgeLean.Foundations.Program.SchoenCycleQuotientBaseAction
import HodgeLean.Foundations.Program.SchoenCycleStep1
import Mathlib.RingTheory.Invariant.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual section-ring extension of a finite categorical quotient satisfies the invariant-extension interface.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_quotient_section_invariant_extension
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    Algebra.IsInvariant Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) G := by
  let W := q.left ⁻¹ᵁ U
  letI : Algebra Γ(Y.left, U) Γ(X.left, W) := (q.left.app U).hom.toAlgebra
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  refine ⟨fun b hb => ?_⟩
  have hi (u : G) : ((a u).left.appLE W W
      (s2e_step1_action_preimage X Y q (a u) (hinv u) U)).hom b = b := by
    have h := hb u⁻¹
    change ((a ((u⁻¹)⁻¹)).left.appLE W W
      (s2e_step1_action_preimage X Y q (a ((u⁻¹)⁻¹)) (hinv ((u⁻¹)⁻¹)) U)).hom b = b at h
    simpa only [inv_inv] using h
  obtain ⟨c, hc, _⟩ := s2e_step1_invariant_affine_descent X Y G a ha1 hamul
    q hinv hquot U hU b hi
  exact ⟨c, hc⟩

end HodgeLean.Foundations.Program
