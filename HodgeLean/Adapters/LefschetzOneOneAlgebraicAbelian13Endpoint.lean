import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian13Comparison
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian12
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian15Boundary
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian16

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open Set Topology
namespace HodgeLean.Adapters

private theorem bh13_regular_boundary_open
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    IsOpen (bh8_regularDomain (dim X.left) f \ abelianExp X ⁻¹'
      (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X))) := by
  have hfc : Continuous f := (hf.contDiff (n := 1)).continuous
  have hfd : Continuous (fderiv ℂ f) :=
    (hf.contDiff (n := 2)).continuous_fderiv (by norm_num)
  have hR : IsOpen (bh8_regularDomain (dim X.left) f) := by
    rw [bh8_regularDomain]
    exact ((isClosed_singleton.preimage hfc).isOpen_compl.union
      (isClosed_singleton.preimage hfd).isOpen_compl)
  exact hR.inter
    (((cycleComponentSingularAnalyticClosedFiltration X x 0).isClosed.preimage
      (continuous_abelianExp X)).isOpen_compl)

private theorem bh13_regular_boundary_compl
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p)) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin (dim X.left) → ℂ)),
      (∀ j, (U j).Nonempty → d j + 2 ≤ dim X.left) ∧
      (∀ j, IsOpen (U j)) ∧ (∀ j, DifferentiableOn ℂ (g j) (U j)) ∧
      (bh8_regularDomain (dim X.left) f \ abelianExp X ⁻¹'
        (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X)))ᶜ =
        ⋃ j, g j '' U j := by
  obtain ⟨d, U, g, hd, hU, hg, hc⟩ :=
    bh15_critical_boundary_stratification X x hx f hf hred
  refine ⟨d, U, g, hd, hU, hg, ?_⟩
  rw [← hc]
  ext p
  simp only [mem_compl_iff, mem_diff, bh8_regularDomain, mem_setOf_eq,
    mem_union, mem_preimage]
  tauto

private theorem bh13_boundary_subset_zero
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left)
    (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hs : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x) :
    abelianExp X ⁻¹'
      (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X)) ⊆
      {p | f p = 0} := by
  intro p hp
  apply (hs p).2
  by_contra hsupport
  exact (cycleComponentSupportComplement_le_smoothAmbientOpen X x hsupport) hp

set_option maxHeartbeats 400000 in
/-- On the regular-domain pair, a reduced equation has the normalized component coclass.
Source: Griffiths--Harris, Chapter 1, section 1, the local divisor class;
`cycleComponentSupportedInjectiveClass_normalization`. -/
theorem bh13_regular_normalization
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (dim X.left) p))
    (hs : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x) :
    relativeCohomologyMap ℚ 2 (bh8_regularInclusion (dim X.left) f)
      (relativeCohomologyMap ℚ 2 (bh8_coverMap X x f hs)
        (complexSupportInjectiveSectionCohomologyEquiv X
          (cycleComponentAnalyticClosedSupport X x) ⊤ 2
          ((rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) 2)
            (cycleComponentSupportedInjectiveClass X x hx)))) =
    relativeCohomologyMap ℚ 2 (bh8_regularInclusion (dim X.left) f)
      (relativeCohomologyMap ℚ 2 (bh8_normalMap (dim X.left) f
        (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt))
        (normalizedPointCoclass 1)) := by
  let B : Set (Fin (dim X.left) → ℂ) := abelianExp X ⁻¹'
    (cycleComponentSingularAnalyticClosedFiltration X x 0 : Set (ComplexPoint X))
  let O : Set (Fin (dim X.left) → ℂ) := bh8_regularDomain (dim X.left) f \ B
  let Z : Set (Fin (dim X.left) → ℂ) := {p | f p = 0}
  have hO : IsOpen O := bh13_regular_boundary_open X x f hf
  obtain ⟨d, U, g, hd, hU, hg, hcover⟩ :=
    bh13_regular_boundary_compl X x hx f hf hred
  have hBZ : B ⊆ Z := bh13_boundary_subset_zero X x f hs
  have hsub : Zᶜ ⊆ O := by
    intro p hp
    refine ⟨Or.inl hp, ?_⟩
    exact fun hpB ↦ hp (hBZ hpB)
  let rO : TopPair.ofSubset (X := TopCat.of O) {p | p.1 ∉ Z} ⟶
      bh8_equationPair (dim X.left) f :=
    TopPair.ofSubsetHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (fun _ h ↦ h)
  have hr_inj : Function.Injective (relativeCohomologyMap ℚ 2 rO) := by
    exact bh16_cover_nested_restriction (dim X.left) O hO d U g hU hg hd hcover Z hsub
  let a := relativeCohomologyMap ℚ 2 (bh8_coverMap X x f hs)
    (complexSupportInjectiveSectionCohomologyEquiv X
      (cycleComponentAnalyticClosedSupport X x) ⊤ 2
      ((rationalSupportAddEquivSupportedInjectiveHomology X
        (cycleComponentAnalyticClosedSupport X x) 2)
        (cycleComponentSupportedInjectiveClass X x hx)))
  let b := relativeCohomologyMap ℚ 2 (bh8_normalMap (dim X.left) f
      (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt))
    (normalizedPointCoclass 1)
  have hOR : O ⊆ bh8_regularDomain (dim X.left) f := fun _ hp ↦ hp.1
  let iTop : neighborhoodSupportComplementPair
      (univ : Set (Fin (dim X.left) → ℂ)) {q | f q = 0} ⟶
      bh8_equationPair (dim X.left) f :=
    TopPair.ofSubsetHom
      (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim X.left) → ℂ)) ↦ y.1,
        continuous_subtype_val⟩) (fun _ h ↦ h)
  let iO := neighborhoodSupportInclusionPairMap
    (show O ⊆ (univ : Set (Fin (dim X.left) → ℂ)) from Set.subset_univ O)
    {q | f q = 0}
  have hrO : rO = iO ≫ iTop := by rfl
  have habO : relativeCohomologyMap ℚ 2 rO a = relativeCohomologyMap ℚ 2 rO b := by
    rw [hrO, relativeCohomologyMap_comp]
    apply (bh12_regular_germs_injective (dim X.left) f hf ⟨O, hO⟩ hOR)
    funext p
    simp only [LinearMap.comp_apply]
    dsimp only [iO]
    rw [supportRelativeCohomologyGerm_restrict
      (X := TopCat.of (Fin (dim X.left) → ℂ)) (S := Z) (n := 2)
      (U := ⟨O, hO⟩) (V := ⊤) le_top,
      supportRelativeCohomologyGerm_restrict
        (X := TopCat.of (Fin (dim X.left) → ℂ)) (S := Z) (n := 2)
        (U := ⟨O, hO⟩) (V := ⊤) le_top]
    by_cases hp : f p = 0
    · apply bh13_smooth_local_comparison X x hx f hf hs p hp
      · exact p.property.1.resolve_left (not_ne_iff.mpr hp)
      · exact p.property.2
    · have hZ : IsClosed Z := by
        exact isClosed_singleton.preimage (hf.contDiff (n := 1)).continuous
      exact (supportRelativeCohomologyGerm_eq_zero_of_not_mem
        (X := TopCat.of (Fin (dim X.left) → ℂ)) (S := Z) (n := 2)
          hZ ⊤ p (by trivial) hp
          (relativeCohomologyMap ℚ 2 iTop a)).trans
        (supportRelativeCohomologyGerm_eq_zero_of_not_mem
          (X := TopCat.of (Fin (dim X.left) → ℂ)) (S := Z) (n := 2)
            hZ ⊤ p (by trivial) hp
            (relativeCohomologyMap ℚ 2 iTop b)).symm
  have hab : a = b := hr_inj habO
  exact congrArg (relativeCohomologyMap ℚ 2
    (bh8_regularInclusion (dim X.left) f)) hab

end HodgeLean.Adapters
