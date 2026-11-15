import HodgeLean.Foundations.RationalHomologyManifold.Defs

/-! Cap as a map in the cochain variable with a fixed singular cycle.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- With a cycle fixed, cap carries cochain differentials to signed chain differentials.
Source: Hatcher, Algebraic Topology, section 3.3, cap boundary formula.
HC no distance; AV milestone no distance.
-/
theorem fixedCycle_cap_coboundary (X : TopCat.{0}) (p q : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (z : AlgebraicTopology.Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 1))
    (hz : AlgebraicTopology.Simplicial.boundary ℚ (p + q) z = 0) :
    AlgebraicTopology.Simplicial.cap ℚ (p + 1) q
      (AlgebraicTopology.Simplicial.coboundary ℚ p φ)
      (AlgebraicTopology.Simplicial.reassocChain ℚ p q z) =
    (-1 : ℚ) ^ (p + 1) • AlgebraicTopology.Simplicial.boundary ℚ q
      (AlgebraicTopology.Simplicial.cap ℚ p (q + 1) φ z) := by
  have h := LinearMap.congr_fun
    (AlgebraicTopology.Simplicial.cap_coboundary_eq ℚ p q φ) z
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    hz, map_zero, zero_sub, pow_succ, mul_neg_one, neg_smul] using h

#print axioms fixedCycle_cap_coboundary
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reassociation of the total degree preserves the cycle equation.
Source: Hatcher, Algebraic Topology, section 2.1, chain complexes and degree identifications.
HC no distance; AV milestone no distance.
-/
theorem fixedCycle_reassoc (X : TopCat.{0}) (p q : ℕ)
    (z : AlgebraicTopology.Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : AlgebraicTopology.Simplicial.boundary ℚ (p + q + 1) z = 0) :
    AlgebraicTopology.Simplicial.boundary ℚ (p + 1 + q)
      (AlgebraicTopology.Simplicial.reassocChain ℚ p (q + 1) z) = 0 := by
  let K := SingularChainComplex ℚ X
  have ht (m : ℕ) (h : p + q + 1 = m) :
      (K.d (m + 1) m).hom
        ((K.XIsoOfEq (congrArg (fun j => j + 1) h)).hom.hom z) = 0 := by
    cases h
    exact hz
  exact ht (p + 1 + q) (by omega)

#print axioms fixedCycle_reassoc
end HodgeLean.Foundations.RationalHomologyManifold
