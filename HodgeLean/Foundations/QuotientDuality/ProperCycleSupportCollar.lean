import HodgeLean.Foundations.QuotientDuality.ProperCycleCollaredSupportCap

/-! # Actual neighborhood maps retained with supported cap
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual open neighborhood with its original support inclusion, retraction, and deformation.
Source: Hatcher, Algebraic Topology, section 0, neighborhood deformation retractions.
HC no distance; AV milestone no distance. -/
structure ProperCycleSupportCollar (X : TopCat.{0}) (S : Set X) where
  neighborhood : Set X
  isOpen : IsOpen neighborhood
  contains : S ⊆ neighborhood
  inclusion : TopCat.of S ⟶ TopCat.of neighborhood
  retraction : TopCat.of neighborhood ⟶ TopCat.of S
  inclusion_factor : inclusion ≫ (TopPair.ofSubset (X := X) neighborhood).map =
    (TopPair.ofSubset (X := X) S).map
  inclusion_retraction : inclusion ≫ retraction = 𝟙 (TopCat.of S)
  deformation : TopCat.Homotopy (𝟙 (TopCat.of neighborhood)) (retraction ≫ inclusion)

/-- The actual supported cap determined by the retained neighborhood and retraction maps.
Source: Hatcher, Algebraic Topology, section 3.3, cap products with support.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.cap {X : TopCat.{0}} {S : Set X}
    (C : ProperCycleSupportCollar X S) (hS : IsClosed S) (p q : ℕ)
    (c : Homology ℚ X (p + q)) :
    CohomologyWithSupport ℚ X S p →ₗ[ℚ] Homology ℚ (TopCat.of S) q :=
  properCycle_collared_support_cap X S C.neighborhood hS C.isOpen C.contains
    C.retraction p q c

/-- The retained support inclusion carries this actual linear cap to the original absolute cap.
Source: properCycle_collared_support_cap_inclusion.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.cap_inclusion {X : TopCat.{0}} {S : Set X}
    (C : ProperCycleSupportCollar X S) (hS : IsClosed S) (p q : ℕ)
    (c : Homology ℚ X (p + q)) (a : CohomologyWithSupport ℚ X S p) :
    homologyMap ℚ q (TopPair.ofSubset (X := X) S).map (C.cap hS p q c a) =
      capCohomologyLinear ℚ X p q
        ((cochainCohomologyEquiv ℚ X p).symm (forgetSupport ℚ X S p a)) c :=
  properCycle_collared_support_cap_inclusion X S C.neighborhood hS C.isOpen C.contains
    C.inclusion C.retraction C.inclusion_factor C.deformation p q c a

end HodgeLean.Foundations.QuotientDuality
