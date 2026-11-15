import HodgeLean.Foundations.RationalHomologyManifold.CapSmallPrism

/-! Stabilization of the actual cap homotopies near a local zero-cochain region.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Sum the actual subdivision prism applied to each successive subdivided input chain.
Source: Hatcher, Algebraic Topology, section 2.1; the iterated subdivision homotopy.
HC no distance; AV milestone no distance.
-/
def rationalPrismSum (X : TopCat.{0}) (i j m : ℕ) :
    (SingularChainComplex ℚ X).X i ⟶ (SingularChainComplex ℚ X).X j :=
  ∑ k ∈ Finset.range m,
    (rationalSubdivisionIterate X k).f i ≫ (rationalSubdivisionHomotopy X).hom i j

#print axioms rationalPrismSum
/-- Each next subdivision stage adds its actual prism term to the finite homotopy sum.
Source: Hatcher, Algebraic Topology, section 2.1; the finite subdivision-prism sum.
HC no distance; AV milestone no distance.
-/
theorem rationalPrismSum_succ (X : TopCat.{0}) (i j m : ℕ) :
    rationalPrismSum X i j (m + 1) = rationalPrismSum X i j m +
      (rationalSubdivisionIterate X m).f i ≫ (rationalSubdivisionHomotopy X).hom i j := by
  exact Finset.sum_range_succ _ _

#print axioms rationalPrismSum_succ
/-- Relative cap of the finite prism sum stabilizes when its cochain vanishes on one support region.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; eventual vanishing of subordinate prism terms.
HC no distance; AV milestone no distance.
-/
theorem relative_cap_prismSum_stabilizes (X : TopCat.{0}) (U A : Set X)
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) (n p q : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) U).map) p φ = 0)
    (z : (SingularChainComplex ℚ X).X n) :
    ∃ m : ℕ, ∀ r : ℕ,
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f q
        (cap ℚ p q φ (rationalPrismSum X n (p + q) (m + r) z)) =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f q
        (cap ℚ p q φ (rationalPrismSum X n (p + q) m z)) := by
  obtain ⟨m, hm⟩ := relative_cap_subdivision_prism_eventually_zero X U A hU hA hcover n p q φ hφ z
  refine ⟨m, fun r => ?_⟩
  induction r with
  | zero => rw [Nat.add_zero]
  | succ r ih =>
      have hs : rationalPrismSum X n (p + q) (m + (r + 1)) z =
          rationalPrismSum X n (p + q) (m + r) z +
            (rationalSubdivisionHomotopy X).hom n (p + q)
              ((rationalSubdivisionIterate X (m + r)).f n z) := by
        rw [show m + (r + 1) = (m + r) + 1 by omega, rationalPrismSum_succ]
        rfl
      rw [hs, map_add, map_add, hm r, add_zero]
      exact ih

#print axioms relative_cap_prismSum_stabilizes
end HodgeLean.Foundations.RationalHomologyManifold
