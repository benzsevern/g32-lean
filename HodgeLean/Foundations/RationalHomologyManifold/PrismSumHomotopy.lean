import HodgeLean.Foundations.RationalHomologyManifold.PrismCapStabilization

/-! The actual finite prism sum is a homotopy from iterated subdivision to the identity.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Compose the actual left-whiskered subdivision prisms to obtain the iterated homotopy.
Source: Hatcher, Algebraic Topology, section 2.1; iteration of the subdivision prism.
HC no distance; AV milestone no distance.
-/
def rationalPrismSumHomotopy (X : TopCat.{0}) : ∀ m : ℕ,
    Homotopy (rationalSubdivisionIterate X m) (𝟙 (SingularChainComplex ℚ X))
  | 0 => Homotopy.ofEq (rationalSubdivisionIterate_zero X)
  | m + 1 => (Homotopy.ofEq (rationalSubdivisionIterate_succ X m)).trans
      (((rationalSubdivisionHomotopy X).compLeftId (rationalSubdivisionIterate X m)).trans
        (rationalPrismSumHomotopy X m))

#print axioms rationalPrismSumHomotopy
/-- Every component of the iterated homotopy is the finite sum of the actual successive prism components.
Source: Hatcher, Algebraic Topology, section 2.1; the literal iterated subdivision homotopy.
HC no distance; AV milestone no distance.
-/
theorem rationalPrismSumHomotopy_hom (X : TopCat.{0}) (m i j : ℕ) :
    (rationalPrismSumHomotopy X m).hom i j = rationalPrismSum X i j m := by
  induction m with
  | zero =>
      simp only [rationalPrismSumHomotopy, Homotopy.ofEq, rationalPrismSum,
        Finset.range_zero, Finset.sum_empty, Pi.zero_apply]
  | succ m ih =>
      simp only [rationalPrismSumHomotopy, Homotopy.trans, Homotopy.ofEq,
        Homotopy.compLeftId, Homotopy.compLeft, Pi.add_apply, add_zero, zero_add]
      rw [ih, rationalPrismSum_succ, add_comm]

#print axioms rationalPrismSumHomotopy_hom
/-- On an actual positive-degree cycle, the boundary of the finite prism sum is the subdivided cycle minus the original cycle.
Source: Hatcher, Algebraic Topology, section 2.1; the subdivision chain-homotopy identity.
HC no distance; AV milestone no distance.
-/
theorem rationalPrismSum_boundary_on_cycle (X : TopCat.{0}) (n m : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : AlgebraicTopology.Simplicial.boundary ℚ n z = 0) :
    AlgebraicTopology.Simplicial.boundary ℚ (n + 1)
        (rationalPrismSum X (n + 1) (n + 2) m z) =
      (rationalSubdivisionIterate X m).f (n + 1) z - z := by
  let K := SingularChainComplex ℚ X
  have h := (rationalPrismSumHomotopy X m).comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have he := ConcreteCategory.congr_hom h z
  change (rationalSubdivisionIterate X m).f (n + 1) z =
      (rationalPrismSumHomotopy X m).hom n (n + 1) ((K.d (n + 1) n).hom z) +
        (K.d (n + 2) (n + 1)).hom ((rationalPrismSumHomotopy X m).hom (n + 1) (n + 2) z) + z at he
  rw [show (K.d (n + 1) n).hom z = 0 from hz, map_zero, zero_add,
    rationalPrismSumHomotopy_hom] at he
  exact (eq_sub_iff_add_eq).mpr he.symm

#print axioms rationalPrismSum_boundary_on_cycle
end HodgeLean.Foundations.RationalHomologyManifold
