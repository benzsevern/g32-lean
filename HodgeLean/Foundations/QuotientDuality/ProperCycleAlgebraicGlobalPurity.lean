import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicSupportPurity

/-! # Actual supported purity on every open for algebraic closed supports -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular Topology TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal analytic closed support of an algebraic closed subset.
Source: Hartshorne, Algebraic Geometry, II.2; continuity of the underlying-point map.
HC no distance; AV milestone no distance. -/
def properCycle_algebraic_analytic_support (X : Over (Spec ↧ℂ)) (S : Closeds X.left) :
    Closeds (ComplexPoint X) :=
  ⟨Point.underlying ⁻¹' (S : Set X.left),
    S.isClosed.preimage (continuous_underlying_to_zariski X)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Algebraic support dimension and actual ambient local concentration give supported relative vanishing on every original open.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, local support calculations and localization.
HC no distance; AV milestone no distance. -/
lemma properCycle_algebraic_support_relative_vanishes
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]
    [T2Space (ComplexPoint X)] [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (S : Closeds X.left) (d : ℕ) (hdim : topologicalKrullDim S ≤ d)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : ComplexPoint X,
      Subsingleton (orientationGroup (TopCat.of (ComplexPoint X)) j x))
    (n : ℕ) (hbound : n + (2 * d + 1) ≤ N) (U : Opens (ComplexPoint X)) :
    IsZero (RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set (ComplexPoint X))
      (properCycle_algebraic_analytic_support X S : Set (ComplexPoint X))) n) := by
  apply a3b4a_classRelative_vanishing_of_cofinal_local_vanishing
    (TopCat.of (ComplexPoint X)) (properCycle_algebraic_analytic_support X S) U n
  intro j hj x hxU P hxP
  exact properCycle_algebraic_support_cofinal_relative_vanishes X S d hdim N hvan j
    (by omega) x P hxP

end HodgeLean.Foundations.QuotientDuality
