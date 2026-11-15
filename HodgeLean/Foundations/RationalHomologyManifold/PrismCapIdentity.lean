import HodgeLean.Foundations.RationalHomologyManifold.PrismBoundary

/-! The literal cap identity on the finite subdivision prism of a fixed cycle.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Cap on the actual finite prism relates fixed-cycle cap to cap on the subdivided cycle with the original Alexander–Whitney sign.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; subdivision homotopy and the cap boundary formula.
HC no distance; AV milestone no distance.
-/
theorem rationalPrismSum_cap_identity (X : TopCat.{0}) (p q m : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (z : (SingularChainComplex ℚ X).X (p + q))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (p + q) j z = 0) :
    cap ℚ p q φ z =
      cap ℚ p q φ ((rationalSubdivisionIterate X m).f (p + q) z) -
        cap ℚ (p + 1) q (coboundary ℚ p φ)
          (reassocChain ℚ p q (rationalPrismSum X (p + q) (p + q + 1) m z)) -
        (-1 : ℚ) ^ p • boundary ℚ q
          (cap ℚ p (q + 1) φ (rationalPrismSum X (p + q) (p + q + 1) m z)) := by
  have h := LinearMap.congr_fun (cap_coboundary_eq ℚ p q φ)
    (rationalPrismSum X (p + q) (p + q + 1) m z)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h
  rw [rationalPrismSum_boundary_of_cycle X (p + q) m z hz, map_sub] at h
  rw [h]
  have hc (a b c : ChainGroup ℚ (TopCat.toSSet.obj X) q) :
      a = b - (b - a - c) - c := by abel
  exact hc _ _ _

#print axioms rationalPrismSum_cap_identity
end HodgeLean.Foundations.RationalHomologyManifold
