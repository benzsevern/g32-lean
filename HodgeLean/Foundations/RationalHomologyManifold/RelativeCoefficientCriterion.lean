import HodgeLean.Foundations.RationalHomologyManifold.SupportedChainPatching

/-! Coefficient criteria for equality of actual relative chains.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Relative chains agree precisely when their coefficients agree at every simplex absent from the subspace.
Source: Hatcher, Algebraic Topology, section 2.1, the relative singular chain quotient.
HC no distance; AV milestone no distance.
-/
theorem relativeChainProjection_eq_iff_coefficients (P : TopPair.{0}) (n : ℕ)
    (z w : ((chainPairFunctor ℚ).obj P).right.X n) :
    (relativeChainProjection ℚ P).f n z = (relativeChainProjection ℚ P).f n w ↔
      ∀ s, (∀ t, s ≠ (TopCat.toSSet.map P.map).app _ t) →
        (singularChainCoefficient P.fst n s).hom z =
          (singularChainCoefficient P.fst n s).hom w := by
  classical
  constructor
  · intro hp s hs
    have hz := ConcreteCategory.congr_hom (relativeChainCoefficient_projection P n s hs) z
    have hw := ConcreteCategory.congr_hom (relativeChainCoefficient_projection P n s hs) w
    change (relativeChainCoefficient P n s hs).hom ((relativeChainProjection ℚ P).f n z) =
      (singularChainCoefficient P.fst n s).hom z at hz
    change (relativeChainCoefficient P n s hs).hom ((relativeChainProjection ℚ P).f n w) =
      (singularChainCoefficient P.fst n s).hom w at hw
    exact hz.symm.trans ((congrArg (relativeChainCoefficient P n s hs).hom hp).trans hw)
  · intro h
    apply (relativeChainProjection_eq_iff P n z w).mpr
    apply singularChain_lift_of_coefficient_support P.map n (z - w)
    intro s hs
    by_contra hn
    apply hs
    have hc := h s (fun t heq => hn ⟨t, heq.symm⟩)
    simpa only [map_sub, hc, sub_self]

#print axioms relativeChainProjection_eq_iff_coefficients
end HodgeLean.Foundations.RationalHomologyManifold
