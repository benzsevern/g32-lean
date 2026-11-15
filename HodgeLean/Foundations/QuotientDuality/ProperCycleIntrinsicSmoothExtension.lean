import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothChartOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectedPointValues
import HodgeLean.RealDefs.TopDegreeRank
import HodgeLean.Foundations.Connected

/-! # Original intrinsic top classes on actual smooth projective schemes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- On an original smooth integral projective scheme, the actual ordinary top class has the exact normalization in every originally specified holomorphic chart and generates ordinary top homology.
Source: j5c_exists_complexFundamentalClass; j5d_eq_smul_of_complexFundamentalClass; properCycle_smooth_holomorphic_chart_orientation.
HC no distance; AV milestone no distance. -/
theorem properCycle_smooth_intrinsic_extension
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom] [Smooth V.hom]
    (d : ℕ) [SmoothOfRelativeDimension d V.hom] :
    ∃! c : Homology ℚ (a3b4_an V.hom) (2*d),
      (∀ (e : OpenPartialHomeomorph (ComplexPoint V) (Fin d → ℂ)),
        (∀ i, (f4_analytification V).IsHolFun (fun z : e.source => e z i)) →
        ∀ (x : ComplexPoint V) (hx : x ∈ e.source),
          localOrientation (a3b4_an V.hom) (2*d) c x = localClassOfChart d e x hx) ∧
      Function.Bijective (LinearMap.toSpanSingleton ℚ
        (Homology ℚ (a3b4_an V.hom) (2*d)) c) := by
  let T := a3b4_an V.hom
  let P := TopPair.ofSubset (X := T)
    (((⊤ : Opens (ComplexPoint V)) : Set (ComplexPoint V))ᶜ)
  have hP : P = emptySubspacePair T := by
    change TopPair.ofSubset (X := T) (((⊤ : Opens (ComplexPoint V)) : Set (ComplexPoint V))ᶜ) =
      TopPair.ofSubset (X := T) ∅
    congr 1
    ext x
    simp
  have hproj : Function.Bijective (relativeHomologyProjection ℚ P (2*d)).hom := by
    rw [hP]
    exact (homologyEmptySubspaceIso ℚ T (2*d)).toLinearEquiv.bijective
  obtain ⟨w, hw⟩ := j5c_exists_complexFundamentalClass V d
  obtain ⟨c, hc⟩ := hproj.surjective w
  have hlocal (x : ComplexPoint V) : localOrientation T (2*d) c x = complexLocalOrientation V d x := by
    have hx := hw x
    rw [← hc] at hx
    exact (properCycle_support_projection_point_value T
      ((⊤ : Opens (ComplexPoint V)) : Set (ComplexPoint V)) (2*d) c x (Opens.mem_top x)).symm.trans hx
  have hnorm : ∀ (e : OpenPartialHomeomorph (ComplexPoint V) (Fin d → ℂ)),
      (∀ i, (f4_analytification V).IsHolFun (fun z : e.source => e z i)) →
      ∀ (x : ComplexPoint V) (hx : x ∈ e.source),
        localOrientation T (2*d) c x = localClassOfChart d e x hx := by
    intro e he x hx
    exact (hlocal x).trans (properCycle_smooth_holomorphic_chart_orientation V d e he x hx)
  let hconn : ComplexPointsPreconnected :=
    { preconnected := fun Y _ _ _ => by
        letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
        letI := AlgebraicGeometry.ComplexPoint.connectedSpace Y
        infer_instance }
  have hspan (b : Homology ℚ T (2*d)) : ∃ q : ℚ, q • c = b := by
    obtain ⟨q, hq⟩ := j5d_eq_smul_of_complexFundamentalClass hconn V d w hw
      ((relativeHomologyProjection ℚ P (2*d)).hom b)
    refine ⟨q, hproj.injective ?_⟩
    rw [map_smul, hc]
    exact hq.symm
  letI : QuasiSeparatedSpace V.left := quasiSeparatedSpace_of_quasiSeparated V.hom
  letI := AlgebraicGeometry.ComplexPoint.connectedSpace V
  obtain ⟨x⟩ := (inferInstance : Nonempty (ComplexPoint V))
  have hc0 : c ≠ 0 := by
    intro hz
    have hh := hlocal x
    simp only [hz, localOrientation, map_zero] at hh
    exact (localClassOfChart_ne_zero d (localChart V d x) x
      (mem_localChart_source V d x)) hh.symm
  have hgen : Function.Bijective (LinearMap.toSpanSingleton ℚ (Homology ℚ T (2*d)) c) :=
    ⟨fun a b hab => smul_left_injective ℚ hc0 hab, hspan⟩
  refine ⟨c, ⟨hnorm, hgen⟩, ?_⟩
  intro b hb
  obtain ⟨q, hq⟩ := hspan b
  have hh := hb.1 (localChart V d x) (properCycle_smooth_local_chart_holomorphic V d x)
    x (mem_localChart_source V d x)
  rw [← hq] at hh
  change (relativeHomologyProjection ℚ (pointComplementPair x) (2*d)).hom (q • c) = _ at hh
  rw [map_smul] at hh
  change q • localOrientation T (2*d) c x = _ at hh
  rw [hnorm (localChart V d x) (properCycle_smooth_local_chart_holomorphic V d x)
    x (mem_localChart_source V d x)] at hh
  have hq1 : q = 1 := smul_left_injective ℚ
    (localClassOfChart_ne_zero d (localChart V d x) x (mem_localChart_source V d x))
      (by simpa only [one_smul] using hh)
  rw [hq1, one_smul] at hq
  exact hq.symm

end HodgeLean.Foundations.QuotientDuality
