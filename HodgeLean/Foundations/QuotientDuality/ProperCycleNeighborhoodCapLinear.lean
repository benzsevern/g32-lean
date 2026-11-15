import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCap

/-! # The actual neighborhood cap as a linear map in supported cohomology
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The original excised neighborhood cap, with its ambient homology argument fixed, is a linear map on the original supported group.
Source: Hatcher, Algebraic Topology, section 3.3, bilinearity of cap products and closed-support excision.
HC no distance; AV milestone no distance. -/
def properCycle_neighborhood_cap_linear
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (p q : ℕ) (c : Homology ℚ X (p + q)) :
    CohomologyWithSupport ℚ X S p →ₗ[ℚ] Homology ℚ (TopCat.of U) q :=
  let f := b6m_subspacePairMap X U Sᶜ
  let e := LinearEquiv.ofBijective (relativeHomologyMap ℚ (p + q) f)
    (b6m_closed_support_excision_bijective ℚ hU hS hSU (p + q))
  let d := e.symm ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) Sᶜ) (p + q)).hom c)
  ((relativeCapCohomologyLinear ℚ
    (TopPair.ofSubset (X := TopCat.of U) (Subtype.val ⁻¹' Sᶜ)) p q).flip d).comp
      (relativeCohomologyMap ℚ p f)

/-- Evaluation retains the literal original neighborhood cap.
Source: properCycle_neighborhood_cap.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_cap_linear_apply
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (p q : ℕ) (c : Homology ℚ X (p + q)) (a : CohomologyWithSupport ℚ X S p) :
    properCycle_neighborhood_cap_linear X S U hS hU hSU p q c a =
      properCycle_neighborhood_cap X S U hS hU hSU p q a c := rfl

end HodgeLean.Foundations.QuotientDuality
