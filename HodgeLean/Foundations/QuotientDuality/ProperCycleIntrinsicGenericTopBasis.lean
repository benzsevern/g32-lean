import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSmoothOpenBoundary
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothOpenTopBasis
import HodgeLean.Adapters.NormalConeB4aGysinReducedClosedDimension

/-! # Original intrinsic ordinary top bases from actual projective boundary geometry -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- An original positive-dimensional integral projective scheme has an actual ordinary top homology basis canonically normalized on an actual affine smooth generic open, using its original smaller algebraic boundary.
Source: properCycle_intrinsic_smooth_open_small_boundary; properCycle_projective_pointed_boundary_projection_bijective; properCycle_smooth_open_normalized_top_basis.
HC no distance; AV milestone no distance. -/
theorem properCycle_intrinsic_generic_top_basis
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (d : ℕ) (hd : 0 < d) (hdim : topologicalKrullDim X.left = (d : ℕ)) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ genericPoint X.left ∈ U ∧
      ∃ hs : SmoothOfRelativeDimension d (openScheme X U).hom,
        ∃ c : Homology ℚ (a3b4_an X.hom) (2*d),
          (∀ y : ComplexPoint (openScheme X U),
            localOrientation (a3b4_an X.hom) (2*d) c (Point.map (openInclusion X U) y) =
              @properCycle_open_smooth_orientation X U d hs y) ∧
          Function.Bijective (LinearMap.toSpanSingleton ℚ
            (Homology ℚ (a3b4_an X.hom) (2*d)) c) := by
  classical
  obtain ⟨U, hU, hg, hs, hbdim⟩ := properCycle_intrinsic_smooth_open_small_boundary X d hdim
  let Y := openScheme X U
  letI : Nonempty U := ⟨⟨genericPoint X.left, hg⟩⟩
  letI : Nonempty Y.left := inferInstanceAs (Nonempty U.toScheme)
  letI : IsIntegral Y.left := isIntegral_of_isOpenImmersion U.ι
  letI : IsAffine Y.left := hU
  letI : SmoothOfRelativeDimension d Y.hom := hs
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth d Y.hom
  letI : QuasiCompact Y.hom := inferInstance
  letI : IsSeparated Y.hom := inferInstance
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  letI := AlgebraicGeometry.ComplexPoint.connectedSpace Y
  obtain ⟨y₀⟩ := (inferInstance : Nonempty (ComplexPoint Y))
  let B : Closeds X.left := U.compl
  let Z := Over.mk (reducedClosedStructureMap X.hom B)
  let i := properCycle_reduced_closed_map X B
  have hdimZ : topologicalKrullDim Z.left ≤ (d-1 : ℕ) := by
    change topologicalKrullDim (reducedClosedSubscheme B) ≤ (d-1 : ℕ)
    rw [a3b4a_gysin_reduced_closed_dimension_eq]
    exact hbdim
  have hrange : Set.range (Point.map i) = {x : ComplexPoint X | x.underlying ∈ B} := by
    rw [range_map_of_closedImmersion]
    change {x : ComplexPoint X | x.underlying ∈ Set.range (reducedClosedSubschemeι B)} = _
    rw [range_reducedClosedSubschemeι]
    rfl
  have hy₀ : Point.map (openInclusion X U) y₀ ∉ Set.range (Point.map i) := by
    rw [hrange]
    exact fun hb => hb (openHomeomorph X U y₀).property
  obtain ⟨N, hN, hBN, hyN, hproj⟩ := properCycle_projective_pointed_boundary_projection_bijective
    X Z i (d-1) hdimZ (Point.map (openInclusion X U) y₀) hy₀
  have hcover : ∀ x : ComplexPoint X, x ∉ N → x ∈ Set.range (Point.map (openInclusion X U)) := by
    intro x hxN
    have hxU : x.underlying ∈ U := by
      by_contra hx
      apply hxN
      apply hBN
      rw [hrange]
      exact hx
    refine ⟨(openHomeomorph X U).symm ⟨x, hxU⟩, ?_⟩
    exact congrArg Subtype.val ((openHomeomorph X U).apply_symm_apply ⟨x, hxU⟩)
  have hdegree : (2*d-1)+1 = 2*d := by omega
  have hp : Function.Bijective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) N) (2*d)).hom := by
    have hh := hproj (2*d-1) (by omega)
    change Function.Bijective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) N) ((2*d-1)+1)).hom at hh
    rw [hdegree] at hh
    exact hh
  obtain ⟨c, hc, hgen⟩ := properCycle_smooth_open_normalized_top_basis X U d N hN hcover hp y₀ hyN
  exact ⟨U, hU, hg, hs, c, hc, hgen⟩

end HodgeLean.Foundations.QuotientDuality
