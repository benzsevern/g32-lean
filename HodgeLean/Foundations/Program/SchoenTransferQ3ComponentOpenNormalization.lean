import HodgeLean.Foundations.Program.SchoenTransferQ3GenericNormalization
import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentTestOpens

/-! Global normalization from calculations on actual generic component opens. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Generic component opens permit simultaneous isolated test-point selection
for the original supported class and its original component family. -/
theorem s4_q3_normalized_of_component_open_calculations
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (hγ : ∀ p ∈ γ.support, Order.coheight p = k)
    (β : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      (a3b4_cycleSupport X.hom γ)ᶜ) (2 * k))
    (hlocal : ∀ p ∈ γ.support, ∃ U : X.left.Opens, p ∈ U ∧
      ∀ x : ComplexPoint X, x.underlying ∈ U →
        x ∈ cycleComponentAnalyticClosedSupport X p →
        (∀ t ∈ γ.support, t ≠ p → x.underlying ∉ closure ({t} : Set X.left)) →
        ∃ (r : ℕ)
          (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
          (hflat : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e y).2 = 0),
          x ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
          ∃ (V : Set (ComplexPoint X)) (hVe : V ⊆ e.source), IsOpen V ∧ x ∈ V ∧
            relativeCohomologyMap ℚ (2 * k)
              (a3b4_neighborhoodPairMap V (a3b4_cycleSupport X.hom γ)) β =
            a3b4_multiplicity X.hom γ x • chartNormalProjectionCoclass (Fin r → ℂ) k e
              (a3b4_cycleSupport X.hom γ) hflat V hVe) :
    a3b4_IsCycleClass X.hom γ k β := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  let I := {p : X.left // p ∈ γ.support}
  letI : Fintype I := (a3b2_support_finite γ).fintype
  choose U hU hcalc using fun i : I => hlocal i.1 i.2
  obtain ⟨a, haC, haB, haU⟩ := s4_q3_regular_component_test_points_in_opens
    X I k Subtype.val Subtype.val_injective (fun i => hγ i.1 i.2) U hU
  apply s4_q3_normalized_of_generic_normal_tests X γ k hγ β a haC haB
  intro i
  apply hcalc i (a i) (haU i) (haC i)
  intro t ht hti hmem
  apply haB i
  apply (hc9k_mem_componentBoundary X (Fintype.card I)
    (Subtype.val ∘ (Fintype.equivFin I).symm) (a i)).mpr
  apply Or.inr
  refine ⟨(Fintype.equivFin I) i, (Fintype.equivFin I) ⟨t, ht⟩, ?_, ?_, ?_⟩
  · intro he
    have he' : i = (⟨t, ht⟩ : I) := (Fintype.equivFin I).injective he
    exact hti (congrArg Subtype.val he').symm
  · simpa only [Function.comp_apply, Equiv.symm_apply_apply] using haC i
  · simp only [Function.comp_apply, Equiv.symm_apply_apply]
    change (a i).underlying ∈ closure ({t} : Set X.left)
    exact hmem

end HodgeLean.Foundations.Program
