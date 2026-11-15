import HodgeLean.Foundations.QuotientDuality.OrientationRelative
import HodgeLean.RealDefs.ComplexFundamentalClassParts.B_HomologyMaps

/-! Relative quotient maps for arbitrary supports and their point restrictions. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

def orbitSupportPairMap (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    (A : Set (orbitSpace G X)) :
    TopPair.ofSubset (X := X) (orbitMap G X ⁻¹' A)ᶜ ⟶
      TopPair.ofSubset (X := orbitSpace G X) Aᶜ :=
  TopPair.ofSubsetHom (orbitMap G X) (fun _ hx => hx)

theorem orbit_support_restriction_square (G : Type) [Group G] (X : TopCat.{0})
    [MulAction G X] (A : Set (orbitSpace G X)) (y : orbitSpace G X) (hy : y ∈ A) :
    supportInclusionPairMap X
        (show {x : X | orbitMap G X x = y} ⊆ orbitMap G X ⁻¹' A from
          fun x hx => by
            change orbitMap G X x ∈ A
            rw [show orbitMap G X x = y from hx]
            exact hy) ≫ orbitComplementPairMap G X y =
      orbitSupportPairMap G X A ≫ supportInclusionPairMap (orbitSpace G X)
        (Set.singleton_subset_iff.mpr hy) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext x <;> rfl

#print axioms orbitSupportPairMap
#print axioms orbit_support_restriction_square
end HodgeLean.Foundations.QuotientDuality
