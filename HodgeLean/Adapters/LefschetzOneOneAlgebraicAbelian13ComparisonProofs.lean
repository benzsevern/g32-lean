import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian13
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian10
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian9Charts

/-! # Equation comparison at a smooth regular anchor

Implication from a smooth component anchor and a regular equation to equality
of the two degree-two germs. No assertion of smoothness at an arbitrary regular
zero is made here. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations Set Topology
namespace HodgeLean.Adapters

private theorem bh13_equation_chart (n : ℕ) (p : Fin n → ℂ)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
    (hp : f p = 0) (hd : fderiv ℂ f p ≠ 0) :
    ∃ d : OpenPartialHomeomorph (Fin n → ℂ)
        ((Fin (n - 1) → ℂ) × (Fin 1 → ℂ)),
      p ∈ d.source ∧ AnalyticOnNhd ℂ d d.source ∧
      AnalyticOnNhd ℂ d.symm d.target ∧
      ∀ y ∈ d.source, (d y).2 0 = f y := by
  cases n with
  | zero =>
    exfalso
    apply hd
    ext v
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv, map_zero]
    rfl
  | succ n => exact bh10_equation_chart n p f hf hp hd

private theorem bh13_chart_transitions (n : ℕ)
    (e d : OpenPartialHomeomorph (Fin n → ℂ)
      ((Fin (n - 1) → ℂ) × (Fin 1 → ℂ)))
    (p : Fin n → ℂ) (he : p ∈ e.source) (hd : p ∈ d.source)
    (hea : AnalyticAt ℂ e p) (hei : AnalyticAt ℂ e.symm (e p))
    (hda : AnalyticAt ℂ d p) (hdi : AnalyticAt ℂ d.symm (d p)) :
    AnalyticAt ℂ (e.symm.trans d) (e p) ∧
    AnalyticAt ℂ (e.symm.trans d).symm ((e.symm.trans d) (e p)) := by
  have hleft : e.symm (e p) = p := e.left_inv he
  have hright : d.symm (d p) = p := d.left_inv hd
  constructor
  · change AnalyticAt ℂ (d ∘ e.symm) (e p)
    exact (hleft.symm ▸ hda).comp hei
  · change AnalyticAt ℂ (e ∘ d.symm) (d (e.symm (e p)))
    rw [hleft]
    exact (hright.symm ▸ hea).comp hdi

private theorem bh13_equation_coclass (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : Continuous f)
    (d : OpenPartialHomeomorph (Fin n → ℂ)
      ((Fin (n - 1) → ℂ) × (Fin 1 → ℂ)))
    (hd : ∀ y ∈ d.source, f y = 0 ↔ (d y).2 = 0)
    (heq : ∀ y ∈ d.source, (d y).2 0 = f y) :
    chartNormalProjectionCoclass (Fin (n - 1) → ℂ) 1 d
      {z | f z = 0} hd d.source (le_refl _) =
    relativeCohomologyMap ℚ 2
      (neighborhoodSupportInclusionPairMap (Set.subset_univ d.source) {z | f z = 0})
      (relativeCohomologyMap ℚ 2
        (show neighborhoodSupportComplementPair (univ : Set (Fin n → ℂ))
          {z | f z = 0} ⟶ bh8_equationPair n f from
          TopPair.ofSubsetHom
            (TopCat.ofHom ⟨fun y : (univ : Set (Fin n → ℂ)) ↦ y.1,
              continuous_subtype_val⟩) (fun _ h ↦ h))
        (relativeCohomologyMap ℚ 2 (bh8_normalMap n f hf)
          (normalizedPointCoclass 1))) := by
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  congr 1
  apply congrArg (relativeCohomologyMap ℚ 2)
  apply MorphismProperty.Arrow.Hom.ext
  · ext y
    apply Subtype.ext
    funext j
    change (d y.1.1).2 j = f y.1.1
    have hj : j = 0 := Subsingleton.elim _ _
    rw [hj]
    exact heq _ y.1.2
  · ext y
    funext j
    change (d y.1).2 j = f y.1
    have hj : j = 0 := Subsingleton.elim _ _
    rw [hj]
    exact heq _ y.2

private theorem bh13_restrict_chart_germ
    (M E : Type) [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph M (E × (Fin 1 → ℂ))) (S : Set M)
    (he : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (p : M) (hp : p ∈ e.source)
    (W : Opens M) (hpW : p ∈ W) (hWe : (W : Set M) ⊆ e.source)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair univ S) 2)
    (ha : relativeCohomologyMap ℚ 2
      (neighborhoodSupportInclusionPairMap (Set.subset_univ (W : Set M)) S) a =
      chartNormalProjectionCoclass E 1 e S he W hWe) :
    supportRelativeCohomologyGerm (TopCat.of M) S 2 ⊤ p (mem_univ p) a =
    supportRelativeCohomologyGerm (TopCat.of M) S 2 ⟨e.source, e.open_source⟩ p hp
      (chartNormalProjectionCoclass E 1 e S he e.source (le_refl _)) := by
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq (TopCat.of M) S 2
    (U := ⊤) (V := ⟨e.source, e.open_source⟩) (W := W)
    (le_top) hWe p hpW
  exact ha.trans (chartNormalProjectionCoclass_restrict E 1 e S he hWe (le_refl _)).symm

set_option maxHeartbeats 400000 in
/-- At a smooth regular anchor, the transported component and equation coclasses have equal germs.
Source: `bh13_exponential_normal_chart`, `bh10_equation_chart`, `bh9_chart_germ`,
and `supportRelativeCohomologyGerm_restrict`. -/
theorem bh13_smooth_local_comparison_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (hx : Order.coheight x = 1)
    (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hs : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x)
    (p : Fin (dim X.left) → ℂ) (hp : f p = 0) (hd : fderiv ℂ f p ≠ 0)
    (ha : abelianExp X p ∈ cycleComponentSmoothSupportAmbientOpen X x) :
    supportRelativeCohomologyGerm (TopCat.of (Fin (dim X.left) → ℂ))
      {z | f z = 0} 2 ⊤ p (mem_univ p)
      (relativeCohomologyMap ℚ 2
        (show neighborhoodSupportComplementPair (univ : Set (Fin (dim X.left) → ℂ))
          {z | f z = 0} ⟶ bh8_equationPair (dim X.left) f from
          TopPair.ofSubsetHom
            (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim X.left) → ℂ)) ↦ y.1,
              continuous_subtype_val⟩) (fun _ h ↦ h)) (relativeCohomologyMap ℚ 2 (bh8_coverMap X x f hs)
        (complexSupportInjectiveSectionCohomologyEquiv X
          (cycleComponentAnalyticClosedSupport X x) ⊤ 2
          ((rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) 2)
            (cycleComponentSupportedInjectiveClass X x hx))))) =
    supportRelativeCohomologyGerm (TopCat.of (Fin (dim X.left) → ℂ))
      {z | f z = 0} 2 ⊤ p (mem_univ p)
      (relativeCohomologyMap ℚ 2
        (show neighborhoodSupportComplementPair (univ : Set (Fin (dim X.left) → ℂ))
          {z | f z = 0} ⟶ bh8_equationPair (dim X.left) f from
          TopPair.ofSubsetHom
            (TopCat.ofHom ⟨fun y : (univ : Set (Fin (dim X.left) → ℂ)) ↦ y.1,
              continuous_subtype_val⟩) (fun _ h ↦ h)) (relativeCohomologyMap ℚ 2 (bh8_normalMap (dim X.left) f
        (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt))
        (normalizedPointCoclass 1))) := by
  obtain ⟨e, he, hpe, hea, hei, W, hpW, hWe, hW⟩ :=
    bh13_exponential_normal_chart X x hx f hf hs p hp ha
  obtain ⟨d, hpd, hda, hdi, hdf⟩ :=
    bh13_equation_chart (dim X.left) p f (hf p (mem_univ p)) hp hd
  have hdS : ∀ y ∈ d.source, f y = 0 ↔ (d y).2 = 0 := by
    intro y hy
    constructor
    · intro hfy
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      exact hj ▸ ((hdf y hy).trans hfy)
    · intro hdy
      exact (hdf y hy).symm.trans (congrFun hdy 0)
  obtain ⟨ht, hti⟩ := bh13_chart_transitions (dim X.left) e d p hpe hpd
    hea hei (hda p hpd) (hdi (d p) (d.map_source hpd))
  refine (bh13_restrict_chart_germ _ _ e {z | f z = 0} he p hpe W hpW hWe _ hW).trans ?_
  refine (bh9_chart_germ _ _ 1 e d {z | f z = 0} he hdS p hpe hpd hp ht hti).trans ?_
  rw [bh13_equation_coclass (dim X.left) f
    (continuous_iff_continuousAt.mpr fun y ↦ (hf y (mem_univ y)).continuousAt) d hdS hdf]
  exact supportRelativeCohomologyGerm_restrict (TopCat.of (Fin (dim X.left) → ℂ))
    {z | f z = 0} 2 (U := ⟨d.source, d.open_source⟩) (V := ⊤)
    le_top p hpd _

end HodgeLean.Adapters
