import HodgeLean.Foundations.QuotientDuality.OrientationRelative
import HodgeLean.Foundations.QuotientDuality.OrientationFiniteSupport

/-! Finite orbit fibers and local homology reductions. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma orbit_fiber_finite (G : Type) [Group G] [Finite G]
    (X : TopCat.{0}) [MulAction G X] (y : orbitSpace G X) :
    {x : X | orbitMap G X x = y}.Finite := by
  obtain ⟨x, rfl⟩ := (Quotient.mk_surjective y)
  apply (Set.finite_range (fun g : G => g • x)).subset
  intro z hz
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hz)
  exact ⟨g, hg⟩

lemma orbit_relative_vanishes (G : Type) [Group G] [Finite G]
    (X : TopCat.{0}) [MulAction G X] [T2Space X] (y : orbitSpace G X) (n i : ℕ)
    (hi : i ≠ n)
    (hvanish : ∀ x j, j ≠ n → Subsingleton (orientationGroup X j x)) :
    Subsingleton (RelativeHomology ℚ (orbitComplementPair G X y) i) := by
  exact finite_support_subsingleton X {x : X | orbitMap G X x = y}
    (orbit_fiber_finite G X y) i (fun x _ => hvanish x i hi)

end HodgeLean.Foundations.QuotientDuality
