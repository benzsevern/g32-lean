import HodgeLean.Foundations.QuotientDuality.ProperCycleAcyclicCoverPieces

/-! # Actual subspace and homeomorphism models for finite cover homology -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal nested subspace of a contained subset is homeomorphic to that original subset.
Source: Munkres, Topology, section 16, subspace topology.
HC no distance; AV milestone no distance. -/
def properCycle_contained_subspace_homeomorph
    (X : TopCat.{0}) (A T : Set X) (hAT : A ⊆ T) :
    {x : T | x.val ∈ A} ≃ₜ A where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hAT x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- An actual homeomorphism transports ordinary rational homology vanishing in every degree.
Source: Hatcher, Algebraic Topology, section 2.1, functorial singular homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_homeomorph_homology_subsingleton
    {X Y : TopCat.{0}} (e : X ≃ₜ Y) (n : ℕ)
    (hY : Subsingleton (Homology ℚ Y n)) : Subsingleton (Homology ℚ X n) := by
  letI := hY
  let E := (((singularHomologyFunctor (ModuleCat ℚ) n).obj
    (ModuleCat.of ℚ ℚ)).mapIso (TopCat.isoOfHomeo e))
  exact E.toLinearEquiv.injective.subsingleton

end HodgeLean.Foundations.QuotientDuality
