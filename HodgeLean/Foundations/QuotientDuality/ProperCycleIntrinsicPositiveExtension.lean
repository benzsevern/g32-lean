import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicChartNormalization

/-! # Original intrinsic top classes on positive-dimensional integral projective schemes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original positive-dimensional integral projective complex scheme has its unique ordinary top class with every originally specified holomorphic chart normalization, generating its actual ordinary top homology.
Source: properCycle_intrinsic_generic_top_basis; properCycle_intrinsic_chart_normalization_from_generic_open.
HC no distance; AV milestone no distance. -/
theorem properCycle_positive_intrinsic_extension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (d : ℕ) (hd : 0 < d) (hdim : topologicalKrullDim X.left = (d : ℕ)) :
    ∃! c : Homology ℚ (a3b4_an X.hom) (2*d),
      (∀ (e : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)),
        (∀ i, (f4_analytification X).IsHolFun (fun z : e.source => e z i)) →
        ∀ (x : ComplexPoint X) (hx : x ∈ e.source),
          localOrientation (a3b4_an X.hom) (2*d) c x = localClassOfChart d e x hx) ∧
      Function.Bijective (LinearMap.toSpanSingleton ℚ
        (Homology ℚ (a3b4_an X.hom) (2*d)) c) := by
  classical
  obtain ⟨U, hU, hg, hs, c, hc, hgen⟩ := properCycle_intrinsic_generic_top_basis X d hd hdim
  let Y := openScheme X U
  letI : SmoothOfRelativeDimension d Y.hom := hs
  have hnorm := properCycle_intrinsic_chart_normalization_from_generic_open X U hU hg d hd hdim c hc
  letI : Nonempty U := ⟨⟨genericPoint X.left, hg⟩⟩
  letI : Nonempty Y.left := inferInstanceAs (Nonempty U.toScheme)
  letI : IsIntegral Y.left := isIntegral_of_isOpenImmersion U.ι
  letI : IsAffine Y.left := hU
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth d Y.hom
  letI : QuasiCompact Y.hom := inferInstance
  letI : IsSeparated Y.hom := inferInstance
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  letI := AlgebraicGeometry.ComplexPoint.connectedSpace Y
  obtain ⟨y₀⟩ := (inferInstance : Nonempty (ComplexPoint Y))
  obtain ⟨e, he, hsource, _⟩ := properCycle_holomorphic_vector_chart_open_transport X U d
    (localChart Y d y₀) (properCycle_smooth_local_chart_holomorphic Y d y₀)
  let x₀ := Point.map (openInclusion X U) y₀
  have hx₀ : x₀ ∈ e.source := by
    rw [hsource]
    exact ⟨y₀, mem_localChart_source Y d y₀, rfl⟩
  refine ⟨c, ⟨hnorm, hgen⟩, ?_⟩
  intro b hb
  obtain ⟨q, hq⟩ := hgen.surjective b
  have hh := hb.1 e he x₀ hx₀
  rw [← hq] at hh
  change (relativeHomologyProjection ℚ (pointComplementPair x₀) (2*d)).hom (q • c) = _ at hh
  rw [map_smul] at hh
  change q • localOrientation (a3b4_an X.hom) (2*d) c x₀ = _ at hh
  rw [hnorm e he x₀ hx₀] at hh
  have hq1 : q = 1 := smul_left_injective ℚ (localClassOfChart_ne_zero d e x₀ hx₀)
    (by simpa only [one_smul] using hh)
  change q • c = b at hq
  rw [hq1, one_smul] at hq
  exact hq.symm

end HodgeLean.Foundations.QuotientDuality
