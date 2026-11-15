import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentComparison
import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentPoints
import HodgeLean.Foundations.Program.SchoenTransferQ3SupportComparison
import HodgeLean.Adapters.KleimanProductProofs

/-! The actual supported sheaf class of a pure rational cycle. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.Foundations HodgeLean.RealDefs
attribute [local irreducible] ccm16_supportedComparison ccm16_supportedLinearEquiv ccm4_supportHModule
namespace HodgeLean.Foundations.Program

/-- The supported comparison of a normalized pure cycle is the finite sum
of its coefficient-weighted canonical component classes. -/
theorem s4_q3_normalized_supported_component_sum
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (hγ : ∀ p ∈ γ.support, Order.coheight p = k)
    (β : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      (a3b4_cycleSupport X.hom γ)ᶜ) (2 * k))
    (hβ : a3b4_IsCycleClass X.hom γ k β) :
    letI : CompactSpace X.left := a3b4_compactSpace X.hom
    let S : Closeds (ComplexPoint X) :=
      ⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩
    let I := {p : X.left // p ∈ γ.support}
    letI : Fintype I := (a3b2_support_finite γ).fintype
    let inc (i : I) : cycleComponentAnalyticClosedSupport X i.1 ≤ S :=
      fun _ h => Set.mem_iUnion₂.mpr ⟨i.1, i.2, h⟩
    β = ccm16_supportedComparison X S (2 * k)
      (∑ i : I, γ i.1 • supportEnlarge X (inc i) (2 * k)
        (cycleComponentSupportedInjectiveClass X i.1 (hγ i.1 i.2))) := by
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
  obtain ⟨u, hu⟩ := (ccm16_supportedComparison X S (2 * k)).surjective β
  let c (i : I) := supportEnlarge X (inc i) (2 * k)
    (cycleComponentSupportedInjectiveClass X i.1 (hγ i.1 i.2))
  change β = ccm16_supportedComparison X S (2 * k) (∑ i : I, γ i.1 • c i)
  rw [← hu]
  apply congrArg (ccm16_supportedComparison X S (2 * k))
  obtain ⟨a, haS, haB⟩ := s4_q3_regular_component_test_points X I k
    Subtype.val Subtype.val_injective (fun i => hγ i.1 i.2)
  have hS : S = ⨆ i : I, cycleComponentAnalyticClosedSupport X i.1 := by
    ext y
    constructor
    · intro hy
      obtain ⟨p, hp, hy⟩ := Set.mem_iUnion₂.mp hy
      exact (ccm5_mem_finiteClosedSup _ y).mpr ⟨⟨p, hp⟩, hy⟩
    · intro hy
      obtain ⟨p, hp⟩ := (ccm5_mem_finiteClosedSup _ y).mp hy
      exact Set.mem_iUnion₂.mpr ⟨p.1, p.2, hp⟩
  apply hc9k_supportedClass_eq_of_generic_germs_aux X I k Subtype.val
    (fun i => hγ i.1 i.2) S hS (2 * k) rfl a haS haB
  intro i
  let eqv := Fintype.equivFin I
  let xs : Fin (Fintype.card I) → X.left := Subtype.val ∘ eqv.symm
  have hsmooth : a i ∈ cycleComponentSmoothSupportAmbientOpen X i.1 := by
    intro hs
    apply haB i
    apply (hc9k_mem_componentBoundary X _ xs (a i)).mpr
    exact Or.inl ⟨eqv i, by simpa [xs, eqv] using hs⟩
  have hother (j : I) (hne : j ≠ i) : a i ∉ cycleComponentAnalyticClosedSupport X j.1 := by
    intro hj
    apply haB i
    apply (hc9k_mem_componentBoundary X _ xs (a i)).mpr
    refine Or.inr ⟨eqv i, eqv j, fun h => hne (eqv.injective h).symm, ?_, ?_⟩
    · simpa [xs, eqv] using haS i
    · simpa [xs, eqv] using hj
  obtain ⟨V, hVo, hxV, hV⟩ := s4_q3_normalized_component_local_comparison X γ k
    i.1 i.2 (hγ i.1 i.2) (a i) hsmooth (haS i)
    (fun t ht hne => hother ⟨t, ht⟩ (fun h => hne (congrArg Subtype.val h)))
    (inc i) β hβ
  have hg : ccm5_supportGerm X S (2 * k) (a i) u =
      ccm5_supportGerm X S (2 * k) (a i) (γ i.1 • c i) := by
    apply s4_q3_supportGerm_eq_of_comparison_restriction X S (2 * k) (a i) ⟨V, hVo⟩ hxV
    change relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap V S)
        ((ccm16_supportedComparison X S (2 * k)) u) = _
    rw [hu, map_smul, s4_q3_supportedComparison_enlarge, map_smul]
    exact hV
  rw [hg, map_sum]
  symm
  apply Finset.sum_eq_single i
  · intro j _ hji
    change ccm5_supportGerm X S (2 * k) (a i)
      (γ j.1 • supportEnlarge X (inc j) (2 * k)
        (cycleComponentSupportedInjectiveClass X j.1 (hγ j.1 j.2))) = 0
    rw [← map_rat_smul (supportEnlarge X (inc j) (2 * k)) (γ j.1)
      (cycleComponentSupportedInjectiveClass X j.1 (hγ j.1 j.2))]
    exact hc9k_supportGerm_enlarge_eq_zero_of_not_mem X (inc j)
      (2 * k) (a i) (hother j hji) _
  · simp

end HodgeLean.Foundations.Program
