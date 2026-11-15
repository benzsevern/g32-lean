import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentNormalization
import HodgeLean.Adapters.NormalConeB4aClassRestriction
import HodgeLean.Adapters.KleimanProductLocal

/-! Comparing a normalized cycle class with its isolated canonical component. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations.Analytic
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.Foundations HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Near an isolated smooth component point, the actual normalized class is
its coefficient times the canonical component class with enlarged support. -/
theorem s4_q3_normalized_component_local_comparison
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (p : X.left) (hpγ : p ∈ γ.support) (hp : Order.coheight p = k)
    (x : ComplexPoint X) (hx : x ∈ cycleComponentSmoothSupportAmbientOpen X p)
    (hxS : x ∈ cycleComponentSupport X p)
    (hother : ∀ t ∈ γ.support, t ≠ p → x.underlying ∉ closure ({t} : Set X.left))
    (hinc : cycleComponentSupport X p ⊆ a3b4_cycleSupport X.hom γ)
    (β : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      (a3b4_cycleSupport X.hom γ)ᶜ) (2 * k))
    (hβ : a3b4_IsCycleClass X.hom γ k β) :
    ∃ V : Set (ComplexPoint X), IsOpen V ∧ x ∈ V ∧
      relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap V (a3b4_cycleSupport X.hom γ)) β =
      γ p • relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap V (a3b4_cycleSupport X.hom γ))
        (relativeCohomologyMap ℚ (2 * k)
          (supportInclusionPairMap (TopCat.of (ComplexPoint X)) hinc)
          (ccm16_supportedComparison X (cycleComponentAnalyticClosedSupport X p) (2 * k)
            (cycleComponentSupportedInjectiveClass X p hp))) := by
  obtain ⟨Z, q, rfl⟩ := Over.mk_surjective X
  let X : Over (Spec ↧ℂ) := Over.mk q
  obtain ⟨e, hf, hxe, he, W, hxW, hWe, hW⟩ :=
    s4_q3_component_class_holomorphic_chart X k p hp x hx hxS
  obtain ⟨O, hOe, hxO, hO⟩ := a3b4a_classSupport_local_eq_component
    X.hom γ p hpγ x hother ⟨e.source, e.open_source⟩ hxe
  change Opens (ComplexPoint X) at O
  let e' := e.restrOpen (O : Set (ComplexPoint X)) O.isOpen
  have he' : a3b4_IsHolChart X.hom e' :=
    ⟨fun j => anb_isHolFun_restrict _ (fun _ h => h.1) (he.1 j),
      fun j => anb_isHolFun_restrict _ (fun _ h => h.1) (he.2 j)⟩
  have hf' : ∀ y ∈ e'.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e' y).2 = 0 :=
    fun y hy => (hO y hy.2).trans (hf y hy.1)
  have hmult : a3b4_multiplicity X.hom γ x = γ p :=
    a3b4a_classMultiplicity_eq_component X.hom γ p hpγ x hxS hother
  obtain ⟨T, hTe', hTo, hxT, hT⟩ := hβ (dim X.left - k) e' hf' x
    ⟨hxe, hxO⟩ (hinc hxS) he'
  change Set (ComplexPoint X) at T
  let V := T ∩ (W : Set (ComplexPoint X))
  have hVT : V ⊆ T := Set.inter_subset_left
  have hVW : V ⊆ (W : Set (ComplexPoint X)) := Set.inter_subset_right
  have hVe : V ⊆ e.source := fun y hy => (hTe' hy.1).1
  have hVe' : V ⊆ e'.source := hVT.trans hTe'
  have hTV := a3b4a_classLocal_normalization_mono e' _ hf' hVT hTe' β _ hT
  rw [hmult] at hTV
  let u := cycleComponentSupportedInjectiveClass X p hp
  have hcmpW : relativeCohomologyMap ℚ (2 * k)
      (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) (cycleComponentSupport X p))
      (ccm16_supportedComparison X (cycleComponentAnalyticClosedSupport X p) (2 * k) u) =
      chartNormalProjectionCoclass (Fin (dim X.left - k) → ℂ) k e
        (cycleComponentSupport X p) hf W hWe :=
    (hc9k_supportedComparison_restrict X (cycleComponentAnalyticClosedSupport X p) W (2 * k) u).trans hW
  have hcmpV := congrArg (relativeCohomologyMap ℚ (2 * k)
    (neighborhoodSupportInclusionPairMap hVW (cycleComponentSupport X p))) hcmpW
  rw [a3b4a_classLocal_restriction_comp, chartNormalProjectionCoclass_restrict] at hcmpV
  refine ⟨V, hTo.inter W.isOpen, ⟨hxT, hxW⟩, hTV.trans ?_⟩
  congr 1
  have hcomm : a3b4_neighborhoodPairMap V (a3b4_cycleSupport X.hom γ) ≫
      supportInclusionPairMap (TopCat.of (ComplexPoint X)) hinc =
      neighborhoodSupportEnlargePairMap V hinc ≫
        a3b4_neighborhoodPairMap V (cycleComponentSupport X p) := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hcomm,
    relativeCohomologyMap_comp, LinearMap.comp_apply, hcmpV]
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  congr 1

end HodgeLean.Foundations.Program
