import HodgeLean.Foundations.Program.SchoenTransferQ3SupportComparison
import HodgeLean.Adapters.KleimanProductProofs
import HodgeLean.Adapters.NormalConeB4aClassExistsPure

/-! Global normalization from actual local tests on the retained components. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
attribute [local irreducible] ccm16_supportedComparison ccm16_supportedLinearEquiv ccm4_supportHModule
namespace HodgeLean.Foundations.Program

/-- One actual local normal-coclass calculation on each regular component
determines normalization of the original global supported class. -/
theorem s4_q3_normalized_of_generic_normal_tests
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (hγ : ∀ p ∈ γ.support, Order.coheight p = k)
    (β : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      (a3b4_cycleSupport X.hom γ)ᶜ) (2 * k))
    (a : {p : X.left // p ∈ γ.support} → ComplexPoint X)
    (haC : ∀ i, a i ∈ cycleComponentAnalyticClosedSupport X i.1)
    (haB : letI : CompactSpace X.left := a3b4_compactSpace X.hom
      let I := {p : X.left // p ∈ γ.support}
      letI : Fintype I := (a3b2_support_finite γ).fintype
      ∀ i, a i ∈ (ccm5_componentBoundary X (Fintype.card I)
        (Subtype.val ∘ (Fintype.equivFin I).symm)).compl)
    (htest : ∀ i,
      ∃ (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
        (hflat : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e y).2 = 0),
        a i ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
        ∃ (V : Set (ComplexPoint X)) (hVe : V ⊆ e.source), IsOpen V ∧ a i ∈ V ∧
          relativeCohomologyMap ℚ (2 * k)
            (a3b4_neighborhoodPairMap V (a3b4_cycleSupport X.hom γ)) β =
          a3b4_multiplicity X.hom γ (a i) • chartNormalProjectionCoclass (Fin r → ℂ) k e
            (a3b4_cycleSupport X.hom γ) hflat V hVe) :
    a3b4_IsCycleClass X.hom γ k β := by
  classical
  obtain ⟨Z, q, rfl⟩ := Over.mk_surjective X
  let X : Over (Spec ↧ℂ) := Over.mk q
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  let S : Closeds (ComplexPoint X) :=
    ⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩
  let I := {p : X.left // p ∈ γ.support}
  letI : Fintype I := (a3b2_support_finite γ).fintype
  obtain ⟨θ, hθ⟩ := a3b4a_cycleClass_exists_of_codimension X.hom γ k
    (fun p hp => (hγ p hp).ge)
  obtain ⟨u, hu⟩ := (ccm16_supportedComparison X S (2 * k)).surjective β
  obtain ⟨v, hv⟩ := (ccm16_supportedComparison X S (2 * k)).surjective θ
  have hS : S = ⨆ i : I, cycleComponentAnalyticClosedSupport X i.1 := by
    ext y
    constructor
    · intro hy
      obtain ⟨p, hp, hy⟩ := Set.mem_iUnion₂.mp hy
      exact (ccm5_mem_finiteClosedSup _ y).mpr ⟨⟨p, hp⟩, hy⟩
    · intro hy
      obtain ⟨p, hp⟩ := (ccm5_mem_finiteClosedSup _ y).mp hy
      exact Set.mem_iUnion₂.mpr ⟨p.1, p.2, hp⟩
  have huv : u = v := by
    apply hc9k_supportedClass_eq_of_generic_germs_aux X I k Subtype.val
      (fun i => hγ i.1 i.2) S hS (2 * k) rfl a haC haB
    intro i
    obtain ⟨r, e, hflat, hxe, he, V, hVe, hVo, hxV, hV⟩ := htest i
    have hxS : a i ∈ a3b4_cycleSupport X.hom γ :=
      Set.mem_iUnion₂.mpr ⟨i.1, i.2, haC i⟩
    obtain ⟨W, hWe, hWo, hxW, hW⟩ := hθ r e hflat (a i) hxe hxS he
    let T := V ∩ W
    have hT : relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap T (a3b4_cycleSupport X.hom γ)) β =
      relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap T (a3b4_cycleSupport X.hom γ)) θ := by
      rw [a3b4a_classLocal_normalization_mono e _ hflat Set.inter_subset_left hVe β _ hV,
        a3b4a_classLocal_normalization_mono e _ hflat Set.inter_subset_right hWe θ _ hW]
    apply s4_q3_supportGerm_eq_of_comparison_restriction X S (2 * k) (a i)
      ⟨T, hVo.inter hWo⟩ ⟨hxV, hxW⟩
    rw [hu, hv]
    exact hT
  have heq : β = θ := hu.symm.trans ((congrArg (ccm16_supportedComparison X S (2 * k)) huv).trans hv)
  rw [heq]
  exact hθ

end HodgeLean.Foundations.Program
