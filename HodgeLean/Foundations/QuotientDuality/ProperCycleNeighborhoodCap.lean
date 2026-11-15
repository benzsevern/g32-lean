import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeCapNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleSamePairCapComparison
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cExcision

/-! # The actual neighborhood cap from the original relative fundamental class -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Restrict the original supported cohomology class and the excised original relative fundamental class to an actual open neighborhood, then apply the original relative cap pairing.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, excision and supported cap products.
HC no distance; AV milestone no distance. -/
noncomputable def properCycle_neighborhood_cap
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (p q : ℕ) (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) :
    Homology ℚ (TopCat.of U) q :=
  let f := b6m_subspacePairMap X U Sᶜ
  let e := LinearEquiv.ofBijective (relativeHomologyMap ℚ (p + q) f)
    (b6m_closed_support_excision_bijective ℚ hU hS hSU (p + q))
  relativeCapCohomologyLinear ℚ (TopPair.ofSubset (X := TopCat.of U) (Subtype.val ⁻¹' Sᶜ)) p q
    (relativeCohomologyMap ℚ p f a)
    (e.symm ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) Sᶜ) (p + q)).hom c))

/-- The neighborhood cap constructed by actual excision maps to the original ordinary cap class under the literal neighborhood inclusion.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, naturality of relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_cap_inclusion
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (p q : ℕ) (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p + q)) :
    homologyMap ℚ q (TopPair.ofSubset (X := X) U).map
      (properCycle_neighborhood_cap X S U hS hU hSU p q a c) =
      capCohomologyLinear ℚ X p q
        ((cochainCohomologyEquiv ℚ X p).symm (forgetSupport ℚ X S p a)) c := by
  let f := b6m_subspacePairMap X U Sᶜ
  let Q := TopPair.ofSubset (X := X) Sᶜ
  let e := LinearEquiv.ofBijective (relativeHomologyMap ℚ (p + q) f)
    (b6m_closed_support_excision_bijective ℚ hU hS hSU (p + q))
  let d := e.symm ((relativeHomologyProjection ℚ Q (p + q)).hom c)
  have he : relativeHomologyMap ℚ (p + q) f d =
      (relativeHomologyProjection ℚ Q (p + q)).hom c := e.apply_symm_apply _
  have hn := properCycle_relative_cap_naturality f p q a d
  have hc := congrArg (relativeCapCohomologyLinear ℚ Q p q a) he
  exact hn.trans (hc.trans (properCycle_same_pair_cap_projection_cohomology Q p q a c).symm)

end HodgeLean.Foundations.QuotientDuality
