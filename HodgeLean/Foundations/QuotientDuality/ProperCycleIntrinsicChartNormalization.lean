import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicChartComplement
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartRestrictionOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicGenericTopBasis

/-! # Original chart normalization across the actual smaller algebraic boundary -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Normalization on an actual smooth affine generic open fixes the exact original local class in every originally specified holomorphic chart across its smaller algebraic boundary.
Source: properCycle_chart_local_scalar; properCycle_chart_open_meets_algebraic_complement; properCycle_open_smooth_orientation_chart.
HC no distance; AV milestone no distance. -/
theorem properCycle_intrinsic_chart_normalization_from_generic_open
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) (hg : genericPoint X.left ∈ U)
    (d : ℕ) (hd : 0 < d) (hdim : topologicalKrullDim X.left = (d : ℕ))
    [SmoothOfRelativeDimension d (openScheme X U).hom]
    (c : Homology ℚ (a3b4_an X.hom) (2*d))
    (hc : ∀ y : ComplexPoint (openScheme X U),
      localOrientation (a3b4_an X.hom) (2*d) c (Point.map (openInclusion X U) y) =
        properCycle_open_smooth_orientation X U d y) :
    ∀ (e : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)),
      (∀ i, (f4_analytification X).IsHolFun (fun z : e.source => e z i)) →
      ∀ (x : ComplexPoint X) (hx : x ∈ e.source),
        localOrientation (a3b4_an X.hom) (2*d) c x = localClassOfChart d e x hx := by
  classical
  let Y := openScheme X U
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  letI : IsAffine Y.left := hU
  letI : QuasiCompact Y.hom := inferInstance
  letI : IsSeparated Y.hom := inferInstance
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian X.hom }
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (a3b4_an X.hom) := f4_t2Space X
  let B : Closeds X.left := U.compl
  have hproper : (B : Set X.left) ≠ Set.univ := by
    intro he
    have hh : genericPoint X.left ∈ (B : Set X.left) := by rw [he]; trivial
    exact hh hg
  have hdimB : topologicalKrullDim B ≤ (d-1 : ℕ) :=
    properCycle_dimension_le_pred_of_lt _ d
      (topologicalKrullDim_lt_of_isClosed_of_ne_univ B.isClosed hproper hdim.le)
  intro e he x hx
  obtain ⟨W, hxW, hW, q, hq⟩ := properCycle_chart_local_scalar (a3b4_an X.hom) d e c x hx
  obtain ⟨z, hzW, hzB⟩ := properCycle_chart_open_meets_algebraic_complement
    X B (d-1) hdimB d (by omega) e W ⟨x, hxW⟩ hW
  have hzU : z.underlying ∈ U := not_not.mp hzB
  let y : ComplexPoint Y := (openHomeomorph X U).symm ⟨z, hzU⟩
  let f := Point.map (openInclusion X U)
  have hy : f y = z := congrArg Subtype.val ((openHomeomorph X U).apply_symm_apply ⟨z, hzU⟩)
  have hyW : f y ∈ W := hy.symm ▸ hzW
  have hyS : f y ∈ e.source := hW hyW
  let V : Set (ComplexPoint X) := Set.range f
  have hV : IsOpen V := (ComplexPoint.isOpenEmbedding_map_open X U).isOpen_range
  let E := e.restrOpen V hV
  have hE : ∀ i, (f4_analytification X).IsHolFun (fun z : E.source => E z i) := by
    intro i
    exact anb_isHolFun_restrict (f4_analytification X).atlas Set.inter_subset_left (he i)
  have hμ : properCycle_open_smooth_orientation X U d y = localClassOfChart d e (f y) hyS :=
    (properCycle_open_smooth_orientation_chart X U d E hE Set.inter_subset_right y
      ⟨hyS, ⟨y, rfl⟩⟩).trans
      (properCycle_chart_restr_open_local_class d e V hV (f y) hyS ⟨y, rfl⟩)
  have hreg : localOrientation (a3b4_an X.hom) (2*d) c (f y) =
      localClassOfChart d e (f y) hyS := (hc y).trans hμ
  have hq1 : q = 1 := smul_left_injective ℚ (localClassOfChart_ne_zero d e (f y) hyS) (by
    have hh := hq (f y) hyW
    rw [hreg] at hh
    simpa only [one_smul] using hh.symm)
  rw [hq x hxW, hq1, one_smul]

end HodgeLean.Foundations.QuotientDuality
