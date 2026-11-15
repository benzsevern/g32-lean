import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cGlobalClasses
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cNeighborhoodOrientation
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped Manifold ContDiff
open CategoryTheory Topology Filter Set Asymptotics AlgebraicTopology.Singular
variable (R : Type) [CommRing R] {M : Type} [TopologicalSpace M] (d : ℕ)

set_option backward.isDefEq.respectTransparency false in
theorem b6m_localClassOfChart_eq_of_hasFDerivAt_compressedTransition
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ))
    (hL : Function.Injective L)
    (hderiv : HasFDerivAt (compressedChartTransition d e e' x hx hx') L 0) :
    b6m_localClassOfChart R d e x hx = b6m_localClassOfChart R d e' x hx' := by
  let f := compressedChartTransition d e e' x hx hx'
  let A := complexMatrixOfContinuousLinearMap d L
  have hA : A.det ≠ 0 := complexMatrixOfContinuousLinearMap_det_ne_zero d L hL
  have hAL : (A.mulVecLin.toContinuousLinearMap :
      (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) = L :=
    ContinuousLinearMap.ext (complexMatrixOfContinuousLinearMap_mulVec d L)
  have hderivA : HasFDerivAt f
      (A.mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0 := by
    rw [hAL]
    exact hderiv
  obtain ⟨V, hVsource, hf_ne, hVopen, h0V, hlocal⟩ :=
    b6m_local_complexDifferentiable_invariance R d A hA f.source f.open_source
      (zero_mem_compressedChartTransition_source d e e' x hx hx') f f.continuousOn
      (compressedChartTransition_zero d e e' x hx hx') hderivA
  obtain ⟨c, hc⟩ := (b6m_point_excision_bijective R V 0 hVopen h0V (2 * d)).2 (standardComplexLocalClass R d)
  have hfc : relativeHomologyMap R (2 * d)
      (complexNeighborhoodPuncturedPairMapOf d V f
        (f.continuousOn.mono hVsource) hf_ne) c =
      standardComplexLocalClass R d := hlocal c hc
  have hpair := complexNeighborhoodPuncturedPairMap_compressedChartTransition_comp
    d e e' x hx hx' V hVsource hf_ne
  calc
    relativeHomologyMap R (2 * d) (chartModelEmbeddingPair d e x hx)
        (standardComplexLocalClass R d) =
        relativeHomologyMap R (2 * d) (chartModelEmbeddingPair d e x hx)
          (relativeHomologyMap R (2 * d) (neighborhoodPointComplementPairMap V 0) c) := by
            rw [hc]
    _ = relativeHomologyMap R (2 * d)
        (neighborhoodPointComplementPairMap V 0 ≫ chartModelEmbeddingPair d e x hx) c := by
          rw [relativeHomologyMap_comp]
          rfl
    _ = relativeHomologyMap R (2 * d)
        (complexNeighborhoodPuncturedPairMapOf d V f
            (f.continuousOn.mono hVsource) hf_ne ≫
          chartModelEmbeddingPair d e' x hx') c := by rw [hpair]
    _ = relativeHomologyMap R (2 * d) (chartModelEmbeddingPair d e' x hx')
        (relativeHomologyMap R (2 * d)
          (complexNeighborhoodPuncturedPairMapOf d V f
            (f.continuousOn.mono hVsource) hf_ne) c) := by
              rw [relativeHomologyMap_comp]
              rfl
    _ = relativeHomologyMap R (2 * d) (chartModelEmbeddingPair d e' x hx')
        (standardComplexLocalClass R d) := by rw [hfc]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_localClassOfChart_eq_of_hasFDerivAt_transition
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (T : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ))
    (hT : Function.Injective T)
    (hderiv : HasFDerivAt (fun v ↦ e' (e.symm v)) T (e x)) :
    b6m_localClassOfChart R d e x hx = b6m_localClassOfChart R d e' x hx' := by
  let r := chartRadius d e x hx
  let r' := chartRadius d e' x hx'
  let L₀ : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    (r : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ)
  let L₂ : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    (ContinuousLinearMap.id ℂ (Fin d → ℂ)).comp
      ((r'⁻¹ : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ))
  let L := L₂.comp (T.comp L₀)
  have hfirst : HasFDerivAt
      (OpenPartialHomeomorph.univBall (e x) r :
        (Fin d → ℂ) → (Fin d → ℂ)) L₀ 0 :=
    hasFDerivAt_univBall_complex d (e x) r (chartRadius_pos d e x hx)
  have hlast : HasFDerivAt
      ((OpenPartialHomeomorph.univBall (e' x) r').symm :
        (Fin d → ℂ) → (Fin d → ℂ)) L₂ (e' x) :=
    hasFDerivAt_univBall_symm_complex d (e' x) r' (chartRadius_pos d e' x hx')
  have hfirstN := (piHasFDerivAt_iff_normed d _ L₀ 0).mp hfirst
  have hderivN := (piHasFDerivAt_iff_normed d _ T (e x)).mp hderiv
  have hlastN := (piHasFDerivAt_iff_normed d _ L₂ (e' x)).mp hlast
  have hderivAt : HasFDerivAt (fun v ↦ e' (e.symm v)) T
      (OpenPartialHomeomorph.univBall (e x) r 0) := by
    simpa only [OpenPartialHomeomorph.univBall_apply_zero] using hderivN
  have hmiddle := hderivAt.comp 0 hfirstN
  have hcenter :
      e' (e.symm (OpenPartialHomeomorph.univBall (e x) r 0)) = e' x := by
    rw [OpenPartialHomeomorph.univBall_apply_zero, e.left_inv hx]
  have hlastAt : HasFDerivAt
      ((OpenPartialHomeomorph.univBall (e' x) r').symm :
        (Fin d → ℂ) → (Fin d → ℂ)) L₂
      (e' (e.symm (OpenPartialHomeomorph.univBall (e x) r 0))) := by
    rw [hcenter]
    exact hlastN
  have hcomposedN : HasFDerivAt
      (fun v ↦ (OpenPartialHomeomorph.univBall (e' x) r').symm
        (e' (e.symm (OpenPartialHomeomorph.univBall (e x) r v)))) L 0 := by
    simpa only [L, Function.comp_def] using hlastAt.comp 0 hmiddle
  have hcomposed := (piHasFDerivAt_iff_normed d _ L 0).mpr hcomposedN
  have htransition : HasFDerivAt
      (compressedChartTransition d e e' x hx hx') L 0 := by
    apply hcomposed.congr_of_eventuallyEq
    filter_upwards [] with v
    change (chartModelEmbedding d e' x hx').symm
        (chartModelEmbedding d e x hx v) =
      (OpenPartialHomeomorph.univBall (e' x) r').symm
        (e' (e.symm (OpenPartialHomeomorph.univBall (e x) r v)))
    rfl
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast (chartRadius_pos d e x hx).ne'
  have hr' : (r'⁻¹ : ℂ) ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (chartRadius_pos d e' x hx').ne')
  have hL₀ : Function.Injective L₀ := by
    intro a b hab
    apply smul_right_injective (Fin d → ℂ) hr
    simpa only [L₀, smul_apply, ContinuousLinearMap.id_apply] using hab
  have hL₂ : Function.Injective L₂ := by
    intro a b hab
    apply smul_right_injective (Fin d → ℂ) hr'
    simpa only [L₂, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply] using hab
  have hL : Function.Injective L := by
    intro a b hab
    apply hL₀
    apply hT
    apply hL₂
    simpa only [L, ContinuousLinearMap.comp_apply] using hab
  exact b6m_localClassOfChart_eq_of_hasFDerivAt_compressedTransition R
    d e e' x hx hx' L hL htransition

set_option backward.isDefEq.respectTransparency false in
theorem b6m_localClassOfChart_eq_of_analyticAt_transition
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (hf : AnalyticAt ℂ (fun v ↦ e' (e.symm v)) (e x))
    (hg : AnalyticAt ℂ (fun v ↦ e (e'.symm v)) (e' x)) :
    b6m_localClassOfChart R d e x hx = b6m_localClassOfChart R d e' x hx' := by
  let f : (Fin d → ℂ) → (Fin d → ℂ) := fun v ↦ e' (e.symm v)
  let g : (Fin d → ℂ) → (Fin d → ℂ) := fun v ↦ e (e'.symm v)
  let T := fderiv ℂ f (e x)
  let S := fderiv ℂ g (e' x)
  have hfN : HasFDerivAt f T (e x) := hf.differentiableAt.hasFDerivAt
  have hgN : HasFDerivAt g S (e' x) := hg.differentiableAt.hasFDerivAt
  have hfx : f (e x) = e' x := by
    change e' (e.symm (e x)) = e' x
    rw [e.left_inv hx]
  have hgAt : HasFDerivAt g S (f (e x)) := by
    rw [hfx]
    exact hgN
  have hcomp : HasFDerivAt (g ∘ f) (S.comp T) (e x) := hgAt.comp (e x) hfN
  let t := e.symm.trans e'
  have hsource : e x ∈ t.source := by
    change e x ∈ (e.symm.trans e').source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rw [e.left_inv hx]
    exact hx'
  have hlocalInverse : (g ∘ f) =ᶠ[nhds (e x)] id := by
    filter_upwards [t.open_source.mem_nhds hsource] with v hv
    change t.symm (t v) = v
    exact t.left_inv hv
  have hcompId : HasFDerivAt id (S.comp T) (e x) :=
    hcomp.congr_of_eventuallyEq hlocalInverse.symm
  have hST : S.comp T = ContinuousLinearMap.id ℂ (Fin d → ℂ) :=
    hcompId.unique (hasFDerivAt_id (e x))
  have hT : Function.Injective T := by
    intro a b hab
    calc
      a = (S.comp T) a := by rw [hST, ContinuousLinearMap.id_apply]
      _ = (S.comp T) b := congrArg S hab
      _ = b := by rw [hST, ContinuousLinearMap.id_apply]
  have hfP : HasFDerivAt f T (e x) :=
    (piHasFDerivAt_iff_normed d f T (e x)).mpr hfN
  exact b6m_localClassOfChart_eq_of_hasFDerivAt_transition R d e e' x hx hx' T hT hfP

set_option backward.isDefEq.respectTransparency false in
theorem b6m_chartAt_localClass_eq
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    (z z' q : M)
    (hq : q ∈ (chartAt (Fin d → ℂ) z).source)
    (hq' : q ∈ (chartAt (Fin d → ℂ) z').source) :
    b6m_localClassOfChart R d (chartAt (Fin d → ℂ) z) q hq =
      b6m_localClassOfChart R d (chartAt (Fin d → ℂ) z') q hq' := by
  let T : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    tangentCoordChange 𝓘(ℂ, Fin d → ℂ) z z' q
  have hoverlap : q ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source ∩
      (extChartAt 𝓘(ℂ, Fin d → ℂ) z').source := by
    rw [extChartAt_source, extChartAt_source]
    exact ⟨hq, hq'⟩
  have hraw : HasFDerivAt
      (fun v ↦ (chartAt (Fin d → ℂ) z') ((chartAt (Fin d → ℂ) z).symm v)) T
      (chartAt (Fin d → ℂ) z q) := by
    have h := hasFDerivWithinAt_tangentCoordChange
      (I := 𝓘(ℂ, Fin d → ℂ)) hoverlap
    apply (piHasFDerivAt_iff_normed d _ T (chartAt (Fin d → ℂ) z q)).mpr
    simp only [modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ] at h
    apply h.congr_of_eventuallyEq
    filter_upwards [] with v
    change (chartAt (Fin d → ℂ) z') ((chartAt (Fin d → ℂ) z).symm v) =
      (chartAt (Fin d → ℂ) z') ((chartAt (Fin d → ℂ) z).symm v)
    rfl
  have hT : Function.Injective T := by
    intro a b hab
    have h := congrArg (tangentCoordChange 𝓘(ℂ, Fin d → ℂ) z' z q) hab
    have hback : q ∈ (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source ∩
        (extChartAt 𝓘(ℂ, Fin d → ℂ) z').source ∩
        (extChartAt 𝓘(ℂ, Fin d → ℂ) z).source := ⟨hoverlap, hoverlap.1⟩
    simpa only [T, tangentCoordChange_comp hback,
      tangentCoordChange_self hoverlap.1] using h
  exact b6m_localClassOfChart_eq_of_hasFDerivAt_transition R d
    (chartAt (Fin d → ℂ) z) (chartAt (Fin d → ℂ) z') q hq hq' T hT hraw

def b6m_manifoldLocalClass [ChartedSpace (Fin d → ℂ) M] (x : M) :
    RelativeHomology R (pointComplementPair x) (2 * d) :=
  b6m_localClassOfChart R d (chartAt (Fin d → ℂ) x) x (mem_chart_source _ x)

theorem b6m_manifoldLocalClass_neighborhood
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] (x : M) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧
      ∃ c : RelativeHomology R (TopPair.ofSubset (X := TopCat.of M) (U : Set M)ᶜ) (2 * d),
        ∀ (y : M) (hy : y ∈ U), relativeHomologyMap R (2 * d)
          (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) c =
            b6m_manifoldLocalClass R d y := by
  let e := chartAt (Fin d → ℂ) x
  have hx : x ∈ e.source := mem_chart_source _ x
  refine ⟨chartOrientationNeighborhood d e x hx,
    mem_chartOrientationNeighborhood d e x hx,
    b6m_chartOrientationNeighborhoodClass R d e x hx, ?_⟩
  intro y hy
  rw [b6m_chartOrientationNeighborhoodClass_restrict R d e x hx y hy]
  exact b6m_chartAt_localClass_eq R d x y y
    (chartOrientationNeighborhood_subset_source d e x hx hy) (mem_chart_source _ y)

theorem b6m_manifold_globalOrientation
    [T2Space M] [CompactSpace M] [ChartedSpace (Fin d → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] :
    ∃ w : RelativeHomology R (TopPair.ofSubset
        (((⊤ : TopologicalSpace.Opens M) : Set M)ᶜ : Set (TopCat.of M))) (2 * d),
      ∀ y : M, relativeHomologyMap R (2 * d)
        (supportInclusionPairMap (TopCat.of M)
          (Set.singleton_subset_iff.mpr (TopologicalSpace.Opens.mem_top y))) w =
            b6m_manifoldLocalClass R d y := by
  exact b6m_global_class_exists_of_local_classes R (E := Fin d → ℂ)
    (by simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm])
    (b6m_manifoldLocalClass R d) (b6m_manifoldLocalClass_neighborhood R d)

end HodgeLean.Foundations.Program
