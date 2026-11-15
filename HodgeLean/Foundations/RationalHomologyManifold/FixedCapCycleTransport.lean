import HodgeLean.Foundations.RationalHomologyManifold.ScalarCycleAbsoluteSection
import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapComparison

/-! Actual cycle and local normalization transport for the fixed cap window.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- An actual singular cycle in the fixed-cap total degree has zero differential to every degree.
Source: Hatcher, Algebraic Topology, section 2.1; the shape of the singular chain complex.
HC no distance; AV milestone no distance.
-/
theorem fixedCapCycle_all_differentials (X : TopCat.{0}) (p q : ℕ)
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0) :
    ∀ j, (SingularChainComplex ℚ X).d (p + q + 2) j z = 0 := by
  intro j
  by_cases hj : j = p + q + 1
  · subst j
    exact hz
  · rw [(SingularChainComplex ℚ X).shape (p + q + 2) j
      (by change ¬ j + 1 = p + q + 2; omega)]
    rfl

#print axioms fixedCapCycle_all_differentials
/-- Equality of actual chain degrees transports local normalization of the original singular cycle class without changing the orientation family.
Source: Hatcher, Algebraic Topology, section 2.1; canonical degree transport of actual singular classes and relative projections.
HC no distance; AV milestone no distance.
-/
theorem localization_cycle_degree_transport (X : TopCat.{0}) (n m : ℕ) (h : n = m)
    (o : LocalRationalOrientation X m)
    (w : LinearMap.ker (((SingularChainComplex ℚ X).sc n).g.hom))
    (v : LinearMap.ker (((SingularChainComplex ℚ X).sc m).g.hom))
    (hw : ((SingularChainComplex ℚ X).XIsoOfEq h).hom w.val = v.val)
    (hc : localization X m (((SingularChainComplex ℚ X).sc m).moduleCatHomologyClass v) = o.generator) :
    localization X n (((SingularChainComplex ℚ X).sc n).moduleCatHomologyClass w) =
      (h.symm ▸ o).generator := by
  cases h
  have he : w = v := Subtype.ext hw
  simpa only [he] using hc

#print axioms localization_cycle_degree_transport
end HodgeLean.Foundations.RationalHomologyManifold
