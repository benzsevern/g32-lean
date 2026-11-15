import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupport
import Other.AlgebraicTopology.LocalHomology.PairExcision

/-! # Local relative homology under actual homeomorphisms -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The homeomorphism of point-complement pairs gives the actual local homology comparison.
Source: Hatcher, Algebraic Topology, section 2.1, functoriality of relative homology.
HC no distance; AV milestone no distance. -/
def properCycle_local_homology_homeomorph_iso
    {X Y : TopCat.{0}} (e : X ≃ₜ Y) (x : X) (n : ℕ) :
    orientationGroup X n x ≅ orientationGroup Y n (e x) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
    ((relativeChainFunctor ℚ).mapIso
      (TopPair.isoOfSubset e (by
        intro z
        change (e z ≠ e x) ↔ z ≠ x
        exact not_congr e.injective.eq_iff)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Point excision identifies local homology in an actual open subspace with ambient local homology.
Source: Hatcher, Algebraic Topology, section 2.2, excision.
HC no distance; AV milestone no distance. -/
def properCycle_open_local_homology_iso
    (X : TopCat.{0}) [T1Space X] (W : TopologicalSpace.Opens X) (w : W) (n : ℕ) :
    orientationGroup (TopCat.of W) n w ≅ orientationGroup X n (w : X) := by
  let e : pointComplementPair (M := W) w ≅
      neighborhoodPointComplementPair (W : Set X) (w : X) :=
    TopPair.isoOfSubset (Homeomorph.refl W) (by
      intro z
      change ((z : X) ≠ (w : X)) ↔ z ≠ w
      exact not_congr Subtype.val_injective.eq_iff)
  exact (HomologicalComplex.homologyFunctor (ModuleCat ℚ)
    (ComplexShape.down ℕ) n).mapIso ((relativeChainFunctor ℚ).mapIso e) ≪≫
      neighborhoodPointComplementRelativeHomologyIso (W : Set X) (w : X) W.isOpen w.2 n


end HodgeLean.Foundations.QuotientDuality
