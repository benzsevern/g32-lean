import HodgeLean.Foundations.Program.SchoenCycleClassDefs
import HodgeLean.Foundations.ComplexSheafSingular
import HodgeLean.Adapters.CycleClassFlatPullbackDefs
import HodgeLean.Foundations.Program.SchoenTransferQ3SupportedSum
import HodgeLean.Foundations.Program.SchoenTransferQ3CycleSum

/-! The specified absolute comparison of normalized supported cycle classes. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
attribute [local irreducible] ccm16_supportedComparison ccm16_supportedLinearEquiv ccm4_supportHModule
namespace HodgeLean.Foundations.Program

/-- The canonical singular-to-sheaf comparison sends a normalized supported
class to the sheaf class of its actual rational cycle. -/
theorem s4_q3_normalized_class_to_cycleClass
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (hγ : ∀ p ∈ γ.support, Order.coheight p = k)
    (β : s2e_supportedClass X γ k) (hβ : a3b4_IsCycleClass X.hom γ k β) :
    singularToFieldCohomology ℚ X (2 * k) (s2e_classToAbsolute X γ k β) =
      ccm3_cycleClass X k γ := by
  classical
  obtain ⟨Z, q, rfl⟩ := Over.mk_surjective X
  let X : Over (Spec ↧ℂ) := Over.mk q
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  let S : Closeds (ComplexPoint X) :=
    ⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩
  let I := {p : X.left // p ∈ γ.support}
  letI : Fintype I := (a3b2_support_finite γ).fintype
  let inc (i : I) : cycleComponentAnalyticClosedSupport X i.1 ≤ S :=
    fun _ h => Set.mem_iUnion₂.mpr ⟨i.1, i.2, h⟩
  have hsum : β = ccm16_supportedComparison X S (2 * k)
      (∑ i : I, γ i.1 • supportEnlarge X (inc i) (2 * k)
        (cycleComponentSupportedInjectiveClass X i.1 (hγ i.1 i.2))) :=
    s4_q3_normalized_supported_component_sum X γ k hγ β hβ
  change singularToFieldCohomology ℚ X (2 * k)
    (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X))ᶜ) (2 * k) β) = _
  rw [hsum, ccm16_supportedComparison_forget,
    singularToFieldCohomology_rationalCohomologyLinearEquivSingular,
    map_sum, s4_q3_cycleClass_support_sum X γ k hγ]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_rat_smul, ← forgetSupport_restrict]
  rfl

end HodgeLean.Foundations.Program
