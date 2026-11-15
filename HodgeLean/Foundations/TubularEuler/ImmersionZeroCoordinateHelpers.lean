import HodgeLean.Foundations.Program.SchoenTransferQ3SupportChartCoordinates
import HodgeLean.Adapters.NormalConeB4aClassNormalCharts

/-! # Matching the actual immersion with zero-normal coordinates

The source chart and ambient flattening chart describe the given immersion itself.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry Topology Filter
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Adapters

/-- The specified immersion has literal zero-normal coordinates near its center.
Source: HodgeConjecture, `closedImmersionHolomorphicFlatteningChart_center` and
`HodgeLean.Foundations.Program.s4_q3_support_chart_inverse_zero_eventually`.
HC no distance; AV milestone no distance. -/
theorem immersion_flattening_coordinates_eventually
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y) :
    ∀ᶠ y in 𝓝 z,
      Point.map i y ∈ (ComplexPoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source ∧
      ComplexPoint.closedImmersionHolomorphicFlatteningChart X Y i m d z (Point.map i y) =
        (ComplexPoint.localChart Y m z y, (0 : Fin (d - m) → ℂ)) := by
  let b := ComplexPoint.localChart Y m z
  let a := ComplexPoint.closedImmersionHolomorphicFlatteningChart X Y i m d z
  have hb : z ∈ b.source := ComplexPoint.mem_localChart_source Y m z
  have ha : Point.map i z ∈ a.source :=
    ComplexPoint.closedImmersionHolomorphicFlatteningChart_mem_source X Y i m d z
  have hcenter : a (Point.map i z) = (b z, (0 : Fin (d - m) → ℂ)) :=
    ComplexPoint.closedImmersionHolomorphicFlatteningChart_center X Y i m d z
  have hc : ContinuousAt (fun y => (b y, (0 : Fin (d - m) → ℂ))) z :=
    (b.continuousAt hb).prodMk continuousAt_const
  have ht : ∀ᶠ y in 𝓝 z, (b y, (0 : Fin (d - m) → ℂ)) ∈ a.target := by
    apply hc.eventually
    change a.target ∈ 𝓝 (b z, (0 : Fin (d - m) → ℂ))
    rw [← hcenter]
    exact a.open_target.mem_nhds (a.map_source ha)
  have he := (s4_q3_support_chart_inverse_zero_eventually X Y i m d z).comp_tendsto
    (b.continuousAt hb)
  filter_upwards [ht, he, b.open_source.mem_nhds hb] with y hyt hye hyb
  have hi : a.symm (b y, (0 : Fin (d - m) → ℂ)) = Point.map i y := by
    change a.symm (b y, (0 : Fin (d - m) → ℂ)) = Point.map i (b.symm (b y)) at hye
    simpa only [b.left_inv hyb] using hye
  refine ⟨hi ▸ a.map_target hyt, ?_⟩
  rw [← hi]
  exact a.right_inv hyt

#print axioms immersion_flattening_coordinates_eventually

/-- Matched holomorphic charts retain the specified immersion and its actual image.
Source: HodgeConjecture, `closedImmersionHolomorphicFlatteningChart_mem_range_iff`;
Mathlib, `contMDiffOn_chart`.
HC no distance; AV milestone no distance. -/
theorem immersion_exists_matched_holomorphic_charts
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y) :
    ∃ b : OpenPartialHomeomorph (ComplexPoint Y) (Fin m → ℂ),
      ∃ a : OpenPartialHomeomorph (ComplexPoint X) ((Fin m → ℂ) × (Fin (d - m) → ℂ)),
        z ∈ b.source ∧ Point.map i z ∈ a.source ∧
        a3b4_IsHolChart Y.hom (b.trans
          (Homeomorph.prodUnique (Fin m → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph) ∧
        a3b4_IsHolChart X.hom a ∧
        (∀ y ∈ b.source, Point.map i y ∈ a.source ∧ a (Point.map i y) = (b y, 0)) ∧
        (∀ w ∈ a.source, w ∈ Set.range (Point.map i) ↔ (a w).2 = 0) := by
  let b0 := ComplexPoint.localChart Y m z
  let a0 := ComplexPoint.closedImmersionHolomorphicFlatteningChart X Y i m d z
  have hz0 : z ∈ b0.source := ComplexPoint.mem_localChart_source Y m z
  have hi0 : Point.map i z ∈ a0.source :=
    ComplexPoint.closedImmersionHolomorphicFlatteningChart_mem_source X Y i m d z
  have hreg : ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
      𝓘(ℂ, (Fin m → ℂ) × (Fin (d - m) → ℂ)) ω a0 (Point.map i z) :=
    a3b4a_classStandardFlatteningChart_contMDiffAt X Y i m d z
  obtain ⟨A, hAo, hiA, hhol⟩ :=
    a3b4a_classLocal_exists_holomorphic_restriction X d m (d - m) a0 (Point.map i z) hi0 hreg
  let a := a0.restrOpen A hAo
  have hnear : ∀ᶠ y in 𝓝 z,
      Point.map i y ∈ a.source ∧ a (Point.map i y) = (b0 y, (0 : Fin (d - m) → ℂ)) := by
    filter_upwards [immersion_flattening_coordinates_eventually X Y i m d z,
      (Point.continuous_map i).continuousAt.eventually (hAo.mem_nhds hiA)] with y hy hyA
    exact ⟨⟨hy.1, hyA⟩, hy.2⟩
  obtain ⟨B, hBsub, hBo, hzB⟩ := mem_nhds_iff.mp hnear
  let b := b0.restrOpen B hBo
  have hbi : ∀ y ∈ b.source, Point.map i y ∈ a.source ∧ a (Point.map i y) = (b y, 0) :=
    fun y hy => hBsub hy.2
  refine ⟨b, a, ⟨hz0, hzB⟩, ⟨hi0, hiA⟩, ?_, hhol, hbi, ?_⟩
  · let e := b.trans
      (Homeomorph.prodUnique (Fin m → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph
    have hbreg : ContMDiffOn 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω b0 e.source :=
      (contMDiffOn_chart (I := 𝓘(ℂ, Fin m → ℂ)) (n := ω) (x := z)).mono
        (fun _ hy => hy.1.1)
    constructor
    · intro j
      apply (HodgeLean.Foundations.Analytic.f4_isHolFun_iff_contMDiffOn
        Y m (fun y => (e y).1 j) e.open_source).mpr
      exact (ContinuousLinearMap.proj j).contMDiff.comp_contMDiffOn hbreg
    · intro j
      exact Fin.elim0 j
  · intro w hw
    exact ComplexPoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z w hw.1

#print axioms immersion_exists_matched_holomorphic_charts

end HodgeLean.Foundations.TubularEuler
