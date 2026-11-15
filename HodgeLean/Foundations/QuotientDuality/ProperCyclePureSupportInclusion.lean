import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import HodgeLean.Adapters.NormalConeB4aClassIntersection
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Literal pure prime supports detected by analytic support inclusion
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Analytic inverse images reflect inclusion of actual algebraic closed subsets over the complex base.
Source: JacobsonSpace.closure_inter_closedPoints_eq_closure; pointEquivClosedPoint.
HC no distance; AV milestone no distance. -/
lemma properCycle_algebraic_support_inclusion_of_analytic
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (S T : Closeds X.left)
    (h : (Point.underlying : ComplexPoint X → X.left) ⁻¹' (S : Set X.left) ⊆
      Point.underlying ⁻¹' (T : Set X.left)) : S ≤ T := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hclosed : (S : Set X.left) ∩ closedPoints X.left ⊆ T := by
    rintro x ⟨hxS, hx⟩
    let q := (pointEquivClosedPoint X.hom).symm ⟨x, hx⟩
    let z : ComplexPoint X := Over.homMk q.1 q.2
    have hz : z.underlying = x := pointOfClosedPoint_apply X.hom x hx _
    have hzS : z.underlying ∈ S := hz.symm ▸ hxS
    exact hz ▸ h hzS
  have hdense : closure ((S : Set X.left) ∩ closedPoints X.left) = S :=
    (JacobsonSpace.closure_inter_closedPoints_eq_closure S.isClosed.isLocallyClosed).trans
      S.isClosed.closure_eq
  change (S : Set X.left) ⊆ (T : Set X.left)
  rw [← hdense]
  exact closure_minimal hclosed T.isClosed

/-- Inclusion of actual analytic supports of pure cycles of the same codimension includes every literal source prime in the target prime set.
Source: properCycle_algebraic_support_inclusion_of_analytic; a3b4a_classComponent_intersection_coheight.
HC no distance; AV milestone no distance. -/
lemma properCycle_pure_prime_support_subset
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (k : ℕ) (γ δ : AlgebraicCycle X.left ℚ)
    (hcγ : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (hcδ : ∀ ξ ∈ δ.support, Order.coheight ξ = k)
    (h : a3b4_cycleSupport X.hom γ ⊆ a3b4_cycleSupport X.hom δ) :
    γ.support ⊆ δ.support := by
  have hST := properCycle_algebraic_support_inclusion_of_analytic X
    (a3b4a_classAlgebraicSupport X.hom γ) (a3b4a_classAlgebraicSupport X.hom δ) h
  intro ξ hξ
  have hξS : ξ ∈ a3b4a_classAlgebraicSupport X.hom γ :=
    Set.mem_iUnion₂.mpr ⟨ξ, hξ, subset_closure (Set.mem_singleton ξ)⟩
  obtain ⟨η, hη, hξη⟩ := Set.mem_iUnion₂.mp (hST hξS)
  have he : ξ = η := by
    by_contra hn
    have hl := a3b4a_classComponent_intersection_coheight X.left k ξ η ξ hn
      (hcγ ξ hξ).ge (hcδ η hη).ge (subset_closure (Set.mem_singleton ξ)) hξη
    rw [hcγ ξ hξ] at hl
    have hnat : k + 1 ≤ k := by exact_mod_cast hl
    omega
  exact he.symm ▸ hη

end HodgeLean.Foundations.QuotientDuality
