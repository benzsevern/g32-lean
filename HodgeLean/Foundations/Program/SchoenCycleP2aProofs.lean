import HodgeLean.Foundations.Program.FiniteQuotientSingularComparison
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientPushforward
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientContractible
import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact

/-! # P2a first quotient comparison infrastructure
Implication from an actual finite categorical quotient to quotient topology
and injectivity of rational pullback in every degree. No tower parameters occur.
Invariant-image surjectivity, Künneth and the whole-kernel bound are later units.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program
/-- A finite surjective projective complex morphism has the quotient topology.
Source: Schoen, Compositio Mathematica 65 (1988), Theorem 2.0 construction,
printed pp. 12–13 and quotient passage printed p. 18; proper analytic maps.
This is the topological prerequisite, without a cohomology assertion. -/
theorem s2e_chain_finite_quotient_topology_aux
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q)) :
    Topology.IsQuotientMap (Point.map q) := by
  exact Topology.IsQuotientMap.of_surjective_continuous hsurj (Point.continuous_map q)

/-- Rational pullback is injective for the actual finite group quotient in every degree.
Source: Schoen, Compositio Mathematica 65 (1988), Theorem 2.0 proof,
printed p. 18; Bredon, Sheaf Theory, Chapter V, finite quotient comparison.
Only the injective half is stated; no smoothness of Y is required. -/
theorem s2e_chain_finite_quotient_pullback_injective_aux
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ T, q ≫ g = f)
    (n : ℕ) : Function.Injective (s2e_pullback ℚ q n) := by
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint Y), ParacompactSpace U :=
    s2e_finite_quotient_target_openParacompactSpace X Y G a ha1 hamul q hsurj hinv hquot
  letI := s2e_finite_quotient_pushforward_singular_resolution
    X Y G a ha1 hamul q hsurj hinv hquot
  obtain ⟨L, T, hd, hL⟩ := s2e_finite_quotient_constantSheaf_trace
    X Y G a ha1 hamul q hsurj hinv hquot
  exact singular_cohomology_injective_of_sheaf_trace
    (TopCat.ofHom (Point.continuousMap q))
    (s2e_finite_quotient_target_contractibleOpen_basis X Y G a ha1 hamul q hsurj hinv hquot)
    L T (Fintype.card G) Fintype.card_ne_zero hd hL n

end HodgeLean.Foundations.Program
