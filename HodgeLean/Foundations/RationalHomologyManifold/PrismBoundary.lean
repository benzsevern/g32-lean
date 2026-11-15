import HodgeLean.Foundations.RationalHomologyManifold.PrismSumHomotopy

/-! Boundary of the actual finite subdivision prism in arbitrary natural degree.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The finite prism boundary identity uses the original chain differential in every natural degree.
Source: Hatcher, Algebraic Topology, section 2.1; the subdivision chain homotopy.
HC no distance; AV milestone no distance.
-/
theorem rationalPrismSum_boundary_of_cycle (X : TopCat.{0}) (n m : ℕ)
    (z : (SingularChainComplex ℚ X).X n)
    (hz : ∀ j, (SingularChainComplex ℚ X).d n j z = 0) :
    AlgebraicTopology.Simplicial.boundary ℚ n
        (rationalPrismSum X n (n + 1) m z) =
      (rationalSubdivisionIterate X m).f n z - z := by
  have h := (rationalPrismSumHomotopy X m).comm n
  cases n with
  | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at h
      simp only [zero_add] at h
      have he := ConcreteCategory.congr_hom h z
      change (rationalSubdivisionIterate X m).f 0 z =
        ((SingularChainComplex ℚ X).d 1 0).hom
          ((rationalPrismSumHomotopy X m).hom 0 1 z) + z at he
      rw [rationalPrismSumHomotopy_hom] at he
      exact (eq_sub_iff_add_eq).mpr he.symm
  | succ n =>
      exact rationalPrismSum_boundary_on_cycle X n m z (hz n)

#print axioms rationalPrismSum_boundary_of_cycle
end HodgeLean.Foundations.RationalHomologyManifold
