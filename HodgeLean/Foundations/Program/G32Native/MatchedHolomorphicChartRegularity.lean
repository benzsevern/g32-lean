import HodgeLean.Foundations.TubularEuler.ImmersionZeroCoordinateHelpers
import HodgeLean.Foundations.Program.G32Native.HolomorphicFlatteningInverse

/-! # Matched holomorphic charts retaining their analytic inverses

Both chosen charts are restrictions of the original holomorphic charts.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry Topology Filter
open scoped Manifold ContDiff
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.TubularEuler

theorem immersion_matched_holomorphic_charts_regular
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y) :
    ∃ (b : OpenPartialHomeomorph (ComplexPoint Y) (Fin m → ℂ))
      (a : OpenPartialHomeomorph (ComplexPoint X) ((Fin m → ℂ) × (Fin (d - m) → ℂ))),
      z ∈ b.source ∧ Point.map i z ∈ a.source ∧
      a3b4_IsHolChart Y.hom (b.trans
        (Homeomorph.prodUnique (Fin m → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph) ∧
      a3b4_IsHolChart X.hom a ∧
      (∀ y ∈ b.source, Point.map i y ∈ a.source ∧ a (Point.map i y) = (b y, 0)) ∧
      (∀ w ∈ a.source, w ∈ Set.range (Point.map i) ↔ (a w).2 = 0) ∧
      ContMDiffOn 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω b.symm b.target ∧
      ContMDiffOn 𝓘(ℂ, (Fin m → ℂ) × (Fin (d - m) → ℂ))
        𝓘(ℂ, Fin d → ℂ) ω a.symm a.target := by
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
  refine ⟨b, a, ⟨hz0, hzB⟩, ⟨hi0, hiA⟩, ?_, hhol, hbi, ?_, ?_, ?_⟩
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
  · exact (contMDiffOn_chart_symm (I := 𝓘(ℂ, Fin m → ℂ)) (n := ω) (x := z)).mono
      (fun _ hu => hu.1)
  · intro u hu
    have hy := a0.map_target hu.1
    have h := holomorphic_flattening_inverse_contMDiffAt X Y i m d z (a0.symm u) hy
    rw [a0.right_inv hu.1] at h
    exact h.contMDiffWithinAt

#print axioms immersion_matched_holomorphic_charts_regular
end HodgeLean.Foundations.TubularEuler
